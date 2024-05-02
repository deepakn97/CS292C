// Author: Deepak Nathani
// Category 4: Difny programs with non-recursive method calls

method max(a: int, b: int) returns (r: int)
  ensures r == a || r == b
  ensures r >= a && r >= b
{
  var res: int;
  res := *;
  if a > b {
    res := a;
  } else {
    res := b;
  }
  return res;
}

method secondHighest(arr: array<int>, length: int) returns (dummy: int)
  requires length >= 2
{
  var curr_max: int;
  var second_max: int;
  var i : int;
  curr_max := arr[0];
  second_max := arr[0];

  i := 1;
  while i < length
    invariant 0 <= i <= length
    invariant second_max <= curr_max
    invariant exists j :: 0 <= j < i && curr_max == arr[j]
    invariant exists j :: 0 <= j < i && second_max == arr[j]
    invariant exists j :: 0 <= j < i && second_max <= arr[j]
  {
    if arr[i] >= curr_max {
      second_max := curr_max;
      curr_max := arr[i];
    } else {
      second_max := max(second_max, arr[i]);
    }
    i := i + 1;
  }
  return 0;
}

