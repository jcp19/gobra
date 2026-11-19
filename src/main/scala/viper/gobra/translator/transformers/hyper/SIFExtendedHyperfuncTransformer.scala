// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.gobra.translator.transformers.hyper

import viper.gobra.backend.BackendVerifier
import viper.gobra.frontend.{Config, Hyper}
import viper.gobra.translator.transformers.ViperTransformer
import viper.gobra.translator.util.VprInfo
import viper.silver.ast._
import viper.silver.ast.utility.{Expressions, Simplifier}
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.plugin.sif.{SIFLowExp, SIFRelExp}
import viper.silver.plugin.standard.termination.DecreasesClause
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable

/**
  * Hyperfuncs in the extended SIF encoding (`--hyperMode extended`).
  *
  * The extended encoding is implemented by Viper's SIF plugin, which runs after Gobra and does not support relational
  * functions. This transformation removes hyperfuncs from the program before the plugin runs:
  *
  *  - A hyperfunc that does not read the heap is translated, as in the low-guard encoding with two executions, into an
  *    ordinary function `H(x̄₀, x̄₁)` over the arguments of both executions.
  *  - A hyperfunc that reads the heap cannot be expressed as one function, since the plugin gives each execution its
  *    own copy of the heap. Calls to it are inlined; it must therefore be non-recursive and have a body.
  *  - In assertions, every maximal relational atom that contains a hyperfunc call, e.g. `NonInterf(x, y)` or
  *    `Dist(x) <= eps`, becomes `SIFLowExp(pack(ē), Some(cmp))`, where ē are the atom's unary subexpressions and
  *    `cmp(t, t')` is the atom's two-execution translation over the components of `t` (execution 0) and `t'`
  *    (execution 1). The plugin translates this to `p₁ && p₂ ==> cmp(pack(ē), pack(ē'))`, where ē' are the
  *    subexpressions evaluated in the second execution (with its heap): the atom is assumed and checked only when
  *    both executions are active, as for `low`.
  */
trait SIFExtendedHyperfuncTransformer extends SIFLowGuardTransformer {

  def extendedProgram(p: Program): Either[Seq[AbstractError], Program] = {
    val isHyper = hyperFunctions(p)
    val hyperFuncs = p.functions.filter(f => isHyper(f.name))
    if (hyperFuncs.isEmpty) return Right(p)

    val errors = mutable.ArrayBuffer.empty[AbstractError]
    val functions = p.functions.map(f => f.name -> f).toMap

    // hyperfuncs that read the heap, directly or through other functions; they are inlined
    def readsHeapDirectly(fn: Function): Boolean =
      fn.pres.exists(!_.isPure) || (fn.body.toSeq ++ fn.pres ++ fn.posts).exists(_.exists {
        case _: FieldAccess | _: Unfolding | _: PredicateAccess => true
        case f: FuncApp => functions.get(f.funcname).exists(g => !isHyper(g.name) && g.pres.exists(!_.isPure))
        case _ => false
      })
    val inlined: Set[String] = {
      var acc = hyperFuncs.filter(readsHeapDirectly).map(_.name).toSet
      var changed = true
      while (changed) {
        val next = acc ++ hyperFuncs.filter(f => !acc(f.name) && f.body.exists(_.exists {
          case c: FuncApp => acc(c.funcname)
          case _ => false
        })).map(_.name)
        changed = next != acc
        acc = next
      }
      acc
    }
    for (f <- hyperFuncs if inlined(f.name)) {
      if (f.body.isEmpty) errors += ConsistencyError(s"This hyperfunc reads the heap and has no body; such hyperfuncs are not supported in hyperMode '${Hyper.EnabledExtended.name}', since calls to them are inlined.", f.pos)
      else if (callsTransitively(f.name, f.name, functions, inlined)) errors += ConsistencyError(s"This hyperfunc reads the heap and is recursive; such hyperfuncs are not supported in hyperMode '${Hyper.EnabledExtended.name}', since calls to them are inlined.", f.pos)
    }
    if (errors.nonEmpty) return Left(errors.toSeq)

    val translated: String => Boolean = n => isHyper(n) && !inlined(n)
    val ctx = newContext(_ => false, noDuplicates(p), _ => false, _noMinor = false, translated, Set.empty, 2)
    val translatedFuncs: Map[String, Function] =
      hyperFuncs.filter(f => translated(f.name)).map(f => f.name -> hyperFunction(f, ctx)).toMap

    // the comparator functions and packing domains created for atoms
    val newFunctions = mutable.ArrayBuffer.empty[Function]
    val newDomains = mutable.ArrayBuffer.empty[Domain]
    val usedNames = mutable.Set.empty[String] ++ p.collect { case d: Declaration => d.name }
    def fresh(base: String): String = {
      var i = 0
      while (usedNames(s"$base$i")) i += 1
      usedNames += s"$base$i"
      s"$base$i"
    }

    // inlining of the hyperfuncs that read the heap
    def inline(e: Exp): Exp = e.transform {
      case c: FuncApp if inlined(c.funcname) =>
        val fn = functions(c.funcname)
        val rigid = rigidParameters(fn)
        val body = readRigidParameters(fn.body.get, rigid)
        // the inlined body reports errors at the call. An unfolding in a function body requires only some permission
        // to the predicate instance, so the inlined unfolding uses a wildcard amount.
        val atCall = body.transform {
          case u@Unfolding(pap: PredicateAccessPredicate, b) =>
            Unfolding(PredicateAccessPredicate(pap.loc, Some(WildcardPerm()(c.pos, c.info, c.errT)))(c.pos, c.info, c.errT), b)(u.pos, u.info, u.errT)
        }.transform { case e: Exp => e.withMeta(c.meta) }
        // bound variables get fresh names: the SIF plugin translates quantifiers by name, so a bound variable must not
        // share its name with a variable of the method into which the body is inlined
        val bound = atCall.deepCollect {
          case q: QuantifiedExp => q.variables.map(_.name)
          case l: Let => Seq(l.variable.name)
        }.flatten.toSet
        val renaming = bound.map(n => n -> fresh(s"${n}_hf")).toMap
        val renamed = if (renaming.isEmpty) atCall else atCall.transform {
          case v: LocalVar if renaming.contains(v.name) => v.copy(name = renaming(v.name))(v.pos, v.info, v.errT)
          case d: LocalVarDecl if renaming.contains(d.name) => d.copy(name = renaming(d.name))(d.pos, d.info, d.errT)
        }
        val inst = Expressions.instantiateVariables(renamed, fn.formalArgs, c.args.map(inline), Set.empty[String])
        inline(Simplifier.simplify(inst))
    }

    def isRelationalExp(e: Exp): Boolean = e.exists {
      case _: SIFLowExp | _: SIFRelExp => true
      case f: FuncApp => isHyper(f.funcname)
      case _ => false
    }
    def containsHyperCall(e: Exp): Boolean = e.exists { case f: FuncApp => translated(f.funcname); case _ => false }

    def atom(a: Exp): Exp = {
      // the maximal unary subexpressions of the atom, which are packed and evaluated in each execution by the plugin
      val leaves = mutable.ArrayBuffer.empty[Exp]
      val vars = mutable.ArrayBuffer.empty[LocalVarDecl]
      def abstractLeaves(e: Exp): Exp = e match {
        case _: Literal => e
        case e if !isRelationalExp(e) =>
          val i = leaves.indexOf(e)
          if (i >= 0) vars(i).localVar
          else {
            leaves += e
            vars += LocalVarDecl(fresh("hf_v"), e.typ)(e.pos)
            vars.last.localVar
          }
        case e => e.withChildren(e.children.map {
          case c: Exp => abstractLeaves(c)
          case cs: Seq[_] => cs.map { case c: Exp => abstractLeaves(c); case c => c }
          case c => c
        })
      }
      val abstracted = abstractLeaves(a)
      val boundInside = a.collect { case q: QuantifiedExp => q.variables.map(_.name) }.flatten.toSet
      if (leaves.exists(l => l.exists { case v: LocalVar => boundInside(v.name); case _ => false })) {
        errors += ConsistencyError(s"Quantifiers inside relational expressions with hyperfunc calls are not supported in hyperMode '${Hyper.EnabledExtended.name}': $a", a.pos)
        return a
      }

      val packName = fresh("HfPack")
      val packType = DomainType(packName, Map.empty)(Seq.empty)
      val packFunc = DomainFunc(s"${packName}_pack", vars.toSeq.map(v => LocalVarDecl(v.name, v.typ)()), packType)(domainName = packName)
      val getters = vars.toSeq.zipWithIndex.map { case (v, i) =>
        DomainFunc(s"${packName}_get$i", Seq(LocalVarDecl("t", packType)()), v.typ)(domainName = packName)
      }
      val packApp = DomainFuncApp(packFunc, vars.toSeq.map(_.localVar), Map.empty[TypeVar, Type])()
      val axiom = AnonymousDomainAxiom(
        if (vars.isEmpty) TrueLit()()
        else Forall(vars.toSeq, Seq(Trigger(Seq(packApp))()),
          getters.zip(vars).map { case (g, v) => EqCmp(DomainFuncApp(g, Seq(packApp), Map.empty[TypeVar, Type])(), v.localVar)(): Exp }
            .reduce[Exp](And(_, _)()))()
      )(domainName = packName)
      newDomains += Domain(packName, packFunc +: getters, Seq(axiom))()

      // cmp(t0, t1) = the atom over both executions, with the leaves of execution i read from ti
      val t = Seq(LocalVarDecl("t0", packType)(), LocalVarDecl("t1", packType)())
      val relational = assertion(abstracted, ctx)
      val runVars = ctx.runs.map(r => vars.toSeq.map(v => LocalVar(r.rename(v.name), v.typ)()))
      val projections = ctx.runs.zip(t).map { case (_, ti) =>
        getters.map(g => DomainFuncApp(g, Seq(ti.localVar), Map.empty[TypeVar, Type])(): Exp)
      }
      val body = Expressions.instantiateVariables(relational, runVars.flatten, projections.flatten)
      // the preconditions of the hyperfuncs called in the atom, such that they are checked where the atom occurs
      val pres = body.deepCollect { case c: FuncApp if translatedFuncs.contains(c.funcname) => c }.flatMap { c =>
        val callee = translatedFuncs(c.funcname)
        callee.pres.filterNot(_.isInstanceOf[DecreasesClause]).map(pre => Expressions.instantiateVariables(pre, callee.formalArgs.map(_.localVar), c.args))
      }.distinct
      val cmpName = fresh("hf_cmp")
      newFunctions += Function(cmpName, t, Bool, pres, Seq.empty, Some(body))(a.pos, a.info, a.errT)
      SIFLowExp(DomainFuncApp(packFunc, leaves.toSeq, Map.empty[TypeVar, Type])(a.pos), Some(cmpName))(a.pos, a.info, a.errT)
    }

    // translates an assertion: structural connectives are kept for the plugin, maximal atoms with hyperfunc calls are
    // packed
    def assertionExt(e: Exp): Exp = {
      def go(e: Exp): Exp = e match {
        case e if !containsHyperCall(e) => e
        case a: And => And(go(a.left), go(a.right))(a.pos, a.info, a.errT)
        case i: Implies if !isRelationalExp(i.left) => Implies(i.left, go(i.right))(i.pos, i.info, i.errT)
        case i: Implies => Implies(go(i.left), go(i.right))(i.pos, i.info, i.errT)
        case f: Forall => f.copy(exp = go(f.exp))(f.pos, f.info, f.errT)
        case o: Old => Old(go(o.exp))(o.pos, o.info, o.errT)
        case l: LabelledOld => l.copy(exp = go(l.exp))(l.pos, l.info, l.errT)
        case u: Unfolding => Unfolding(u.acc, go(u.body))(u.pos, u.info, u.errT)
        case e if e.typ == Bool => atom(e)
        case e =>
          errors += ConsistencyError(s"Unexpected non-boolean relational expression: $e", e.pos)
          e
      }
      go(inline(e))
    }

    def stmt(s: Stmt): Stmt = s.transform({
      case a: Assert => a.copy(exp = assertionExt(a.exp))(a.pos, a.info, a.errT)
      case a: Inhale => a.copy(exp = assertionExt(a.exp))(a.pos, a.info, a.errT)
      case a: Exhale => a.copy(exp = assertionExt(a.exp))(a.pos, a.info, a.errT)
      case a: Assume => a.copy(exp = assertionExt(a.exp))(a.pos, a.info, a.errT)
      case w: While => w.copy(invs = w.invs.map(assertionExt), body = stmt(w.body).asInstanceOf[Seqn])(w.pos, w.info, w.errT)
    }, Traverse.TopDown)

    val methods = p.methods.map(m => m.copy(
      pres = m.pres.map(assertionExt),
      posts = m.posts.map(assertionExt),
      body = m.body.map(b => stmt(b).asInstanceOf[Seqn]),
    )(m.pos, m.info, m.errT))
    val predicates = p.predicates.map(q => q.copy(body = q.body.map(assertionExt))(q.pos, q.info, q.errT))
    val otherFunctions = p.functions.filterNot(f => isHyper(f.name))
    val hyperFunctionsTranslated = hyperFuncs.filter(f => translated(f.name)).map(f => translatedFuncs(f.name))

    val result = p.copy(
      domains = p.domains ++ newDomains,
      functions = otherFunctions ++ hyperFunctionsTranslated ++ newFunctions,
      predicates = predicates,
      methods = methods,
    )(p.pos, p.info, p.errT)

    // hyperfunc calls that remain are in positions that the extended encoding cannot express
    result.methods.foreach(m => m.foreach {
      case c: FuncApp if isHyper(c.funcname) && !newFunctions.exists(_.name == c.funcname) =>
        errors += ConsistencyError(s"Calls to hyperfuncs are only supported in assertions in hyperMode '${Hyper.EnabledExtended.name}': $c", c.pos)
      case _ =>
    })
    if (errors.nonEmpty) Left(errors.toSeq.distinct) else Right(result)
  }

  private def callsTransitively(from: String, target: String, functions: Map[String, Function], within: Set[String]): Boolean = {
    def callees(n: String): Set[String] = functions.get(n).toSeq
      .flatMap(f => (f.body.toSeq ++ f.pres ++ f.posts).flatMap(_.deepCollect { case c: FuncApp if within(c.funcname) => c.funcname }))
      .toSet
    var seen = Set.empty[String]
    var frontier = callees(from)
    while (frontier.nonEmpty) {
      if (frontier(target)) return true
      seen ++= frontier
      frontier = frontier.flatMap(callees) -- seen
    }
    false
  }
}

class SIFExtendedHyperfuncTransformerImpl(config: Config) extends ViperTransformer with SIFExtendedHyperfuncTransformer {
  override def transform(task: BackendVerifier.Task): Either[Seq[AbstractError], BackendVerifier.Task] =
    if (config.hyperModeOrDefault != Hyper.EnabledExtended) Right(task)
    else extendedProgram(task.program).map(p => BackendVerifier.Task(removeHyperFuncAnnotations(p), task.backtrack))

  private def removeHyperFuncAnnotations(p: Program): Program =
    p.copy(functions = p.functions.map(f => f.copy()(f.pos, VprInfo.removeHyperFunc(f.info), f.errT)))(p.pos, p.info, p.errT)
}
