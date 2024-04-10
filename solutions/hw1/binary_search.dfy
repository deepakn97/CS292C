predicate Ordered(a: array<int>)
  reads a
{
  forall i: int, j:int ::
    0 <= i <= j < a.Length ==>
      a[i] <= a[j]
}

// Problem 3
method BinarySearch(a: array<int>, x: int)
  returns (found: bool)
  requires Ordered(a)
  ensures
    // <==> means if-and-only if
    // so we're ensuring that
    // - Our search is sound: if we report true, then x must be in a
    // - Our search is complete: if x can be found, then we must report true
    found <==>
    exists i ::
      0 <= i < a.Length &&
      a[i] == x
{
  var len := a.Length;
  var lo := 0;
  var hi := len;
  while lo < hi
    decreases hi - lo
    invariant 0 <= lo <= hi <= len
    // ensure that x is strictly greater than all elements in array a[0:lo]
    invariant forall i : int :: 0 <= i < lo ==> a[i] < x

    //ensure that x is strictly less than all elements in array a[hi:len-1]
    invariant forall i : int :: hi <= i < len ==> a[i] > x
  {
    var mid := (lo + hi) / 2;
    if x == a[mid] {
      return true;
    } else if x < a[mid] {
      hi := mid;
    } else {
      lo := mid + 1;
    }
  }
  return false;
}


// Problem 4
method BuggyBinarySearch(a: array<int>, x: int)
  returns (found: bool)
  requires Ordered(a)
  requires a.Length < 16
  ensures
    found <==>
    exists i : bv4 ::
      0 <= i < a.Length as bv4 &&
      a[i] == x
{
  var len := a.Length as bv4;
  var lo := 0;
  var hi := len;
  while lo < hi
    decreases hi - lo
    invariant 0 <= lo <= hi <= len
    // ensure that x is strictly greater than all elements in array a[0:lo]
    invariant forall i : bv4 :: 0 <= i < lo ==> a[i] < x
    //ensure that x is strictly less than all elements in array a[hi:len-1]
    invariant forall i : bv4 :: hi <= i < len ==> a[i] > x
  {
    var mid := (hi - lo) / 2 + lo;
    if x == a[mid] {
      return true;
    } else if x < a[mid] {
      hi := mid;
    } else {
      lo := mid + 1;
    }
  }
  return false;
}