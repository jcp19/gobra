package pkg

func foo(ghost xs seq[int]) {
  // fails since `2` might exceed length of `xs`
  //:: ExpectedOutput(assignment_error:seq_index_exceeds_length_error)
  ghost ys := xs[2 = 42]
}