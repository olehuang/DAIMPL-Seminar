method Abs(x:int) returns(y:int)
 ensures y >= 0 && (y == x || y== -x)
{
    return if x>= 0 then x else -x;
}