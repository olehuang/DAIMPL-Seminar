predicate sorted(a:array<int>)
 reads a 
{
    forall i,j :: 0 <= i < j <a.Length ==> a[i]<= a[j] 
}

method SelectSort(a: array<int>)
 requires a.Length >= 0
 modifies a 
 ensures sorted(a)
 ensures multiset(a[..]) == old(multiset(a[..]))
{
    var n := a.Length;

    var i:= 0;
    while i < n 
      invariant 0 <= i <= n
      invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
      invariant forall k, l :: 0 <= k < i && i <= l < n ==> a[k] <= a[l] 
      invariant multiset(a[..]) == old(multiset(a[..]))
      modifies a
    {
        var minIndex := i;
        var j:= i+1;

        while j < n
          invariant i < n
          invariant i <= minIndex < n
          invariant i+1 <= j <= n 
          invariant forall k :: i <= k < j ==> a[minIndex] <=  a[k]
          modifies a
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j:= j+1;
        }
        a[i],a[minIndex] := a[minIndex], a[i];
        i:= i+1;
    }
}

method PrintArr(a:array<int>)
   requires a.Length >= 0
{
    print "[";
    var i:= 0;
    while i < a.Length
     invariant 0 <= i <= a.Length
    {
        print a[i];
        if i < a.Length -1{
            print ", ";
        }
        i:=i+1;
    } 
    print "]\n";
}

method Main(){
    print "Hello world\n";
    var a:array<int>:= new int[][4,1,5,8,7,6,2];
    PrintArr(a);
    SelectSort(a);
    PrintArr(a);
}