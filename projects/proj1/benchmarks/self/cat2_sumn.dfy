// Author: Deepak Nathani (dnathani@ucsb.edu)
// Category 2: Difny/\IMP programs with loops but no arrays.
// Sum of the first n integers
//verified

method sumOfN() returns (dummy: int) {
  var n: int;
  var i: int;
  var res: int;
  n := *;
  assume n > 0;
  i := 1;
  res := 1;

  while i <= n
    invariant i <= n + 1
    invariant res == i * (i + 1) / 2
  {
    res := res + (i+1);
    i := i + 1;
  }

  return 0;
}

