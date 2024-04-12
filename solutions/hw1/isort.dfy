ghost predicate Ordered(a: array<int>, left: nat, right: nat)
  reads a
  requires left <= right <= a.Length
{
  forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

method SelectionSort(a: array<int>)
  modifies a
  ensures Ordered(a, 0, a.Length)
{
  for i := 0 to a.Length
    // invariant Ordered(a, 0, i)
  {
    var minValue := a[i];
    var minPos := i;
    for j := i + 1 to a.Length
      invariant minPos < a.Length
    {
      if a[j] < minValue {
        minValue := a[j];
        minPos := j;
      }
    }
    if i != minPos {
      a[i], a[minPos] := minValue, a[i];
    }
  }
}

method Main()
{
  var a: array<int> := new int[3];
  a[0] := 2; a[1] := 4; a[2] := 1;
  SelectionSort(a);
  print a[..];
}