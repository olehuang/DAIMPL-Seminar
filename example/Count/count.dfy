method Count ( n : int) returns ( c : int )
 requires n >= 0  
 ensures c == n  
 {
  c := 0;
  while c < n
   invariant 0 <= c <= n
  {
    c:= c +1;
  }
}