// Author: Deepak Nathani (dnathani@ucsb.edu)
// Category 1: Difny/\IMP programs with no arrays or loops
// Given three time durations (start1, end1) and (start2, end2) and (start3, end3), check if time slot 1 overlaps with time slot 2 or time slot 3.

method Main() returns (dummy: int) {
  var start1 : int;
  var end1 : int;
  var start2 : int;
  var end2 : int;
  var start3 : int;
  var end3 : int;
  var res12: int;
  var res13: int;
  res12 := *;
  res13 := *;
  start1 := 0;
  end1 := 10;
  start2 := 5;
  end2 := 12;
  start3 := 14;
  end3 := 16;

  if start1 > end2 || start2 > end1 {
    res12 := 0;
  }
  else {
    res12 := 1;
  }

  if start1 > end3 || start3 > end1 {
    res13 := 0;
  }
  else {
    res13 := 1;
  }

  assert res12 == 1;
  assert res13 == 0;

  return 0;
}
