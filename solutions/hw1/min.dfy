method min2D(a: array<array<int>>)
  returns (r: int)
  // assume this function can only be called with a non-empty array
  requires a.Length >= 1 && forall i :: 0 <= i < a.Length ==> (a[i].Length >= 1)

  // ensure r is no larger than any element in the array
  ensures forall i :: 0 <= i < a.Length && forall j :: 0 <= j < a[i].Length ==> (r <= a[i][j])

  // ensure r exists in the array
  ensures exists i :: 0 <= i < a.Length && exists j :: 0 <= j < a[i].Length ==> r == a[i][j]
{
  var min := a[0][0];
  for i := 0 to a.Length
    invariant true // replace with your own invariant
  {
    for j := 0 to a[i].Length
      invariant true // replace with your own invariant
    {
      if a[i][j] < min {
        min := a[i][j];
      }
    }
  }
  return min;
}