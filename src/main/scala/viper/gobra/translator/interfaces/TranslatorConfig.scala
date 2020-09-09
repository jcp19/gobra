// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.translator.interfaces

import viper.gobra.translator.interfaces.components._
import viper.gobra.translator.interfaces.translator._

trait TranslatorConfig {

  def seqToSet : SeqToSet
  def seqToMultiset : SeqToMultiset
  def seqMultiplicity : SeqMultiplicity
  def fixpoint: Fixpoint
  def tuple: Tuples
  def typeProperty: TypeProperties

  def ass: Assertions
  def expr: Expressions
  def method: Methods
  def pureMethod: PureMethods
  def predicate: Predicates
  def stmt: Statements
  def typ: Types

  def loc: Locations
}
