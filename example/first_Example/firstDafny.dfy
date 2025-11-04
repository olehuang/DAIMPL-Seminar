 method Max(a:int, b:int ) returns(c:int)
      ensures a >= b ==> c==a
      ensures b > a ==> c==b
   {
     if a >= b {
        return a;
     }else {
        return b;
     }
    }

  method TestMax()
  {
    var res:int := Max(3,4);
    assert res == 4;
   }

method Main(){
    TestMax();
    print "Hello World from Dafny!";
}