package pkg

func foo(b bool) {
  // fails: cannot assign a ghost expression to a non-ghost variable
  //:: ExpectedOutput(type_error)
  xs := seq[1 .. 4]
}
