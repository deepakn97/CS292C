method SelectionSort(a: array<int>)
  modifies a
{
  for i := 0 to a.Length
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