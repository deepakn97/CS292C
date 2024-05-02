// Author: Deepak Nathani (dnathani@ucsb.edu)
// Category 5: Difny programs with recursive method calls

method pow(x: int, n: int) returns (r: int)
  requires x > 0 && n >= 0
{
  var res : int;
  var tmp_res : int;
  res := 1;
  if n > 0 {
    tmp_res := pow(x, n-1);
    res := x * tmp_res;
  }
  else { }
  return res;
}
