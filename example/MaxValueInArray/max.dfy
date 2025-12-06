method Max(a: array<int>) returns (max: int)
  requires a.Length > 0
  ensures max in a[..]
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
{
  max := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= max
    invariant max in a[..]
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}


