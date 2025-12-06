predicate sorted(a:array<int>)
 reads a 
{
    forall i,j :: 0 <= i < j <a.Length ==> a[i]<= a[j] 
}

function findMin(a: array<int>,start:int):int
 requires 0 <= start < a.Length
 reads a
 //ensures start <= findMin(a,start) < a.Length
 //ensures forall k :: start <= k < a.Length ==> a[findMin(a, start)] <= a[k]
 decreases a.Length - start
{
    if start == a.Length - 1 then start
    else
        var rest := findMin(a, start + 1);
        if a[start] <= a[rest] then start else rest
}

method SelectSort(a: array<int>)
 requires a.Length >= 0
 modifies a 
 ensures sorted(a)
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
        var minIndex := findMin(a, i);
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