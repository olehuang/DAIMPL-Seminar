// module LinkedList{
//     class Node{
//         var value : int
//         var next : Node?
//         constructor(v:int,n:Node?)
//            ensures value == v && next == n
//         {
//             value := v;
//             next := n;
//         }
//     }
//     class LinkedList{
//         var head : Node?
//         var length : nat 
//         ghost var Repr: set<Node>
//         constructor()
//            ensures head == null
//            ensures length == 0
//            ensures Repr == {}
//            ensures Valid()
//         {
//             head := null;
//             length := 0;
//             Repr := {};
//         }
//         predicate ValidList(n: Node?,nodes:set<Node>)
//            reads nodes
//         {
//             match n
//             case null => nodes == {}
//             case _=> n in nodes && ValidList(n.next,nodes - {n})
//         }
//         predicate Valid()
//            reads this,Repr
//         {
//             ValidList(head,Repr) &&
//             length == CountLen(head,Repr)
//         }
        
//         function method CountLen(n:Node?,nodes: set<Node>) : nat
//            reads nodes
//            requires ValidList(n,nodes)
//            decreases nodes
//         {
//             if n == null then 0 else 1 + CountLen(n.next , nodes - {n})
//         }
//         method Insert(v:int)
//            modifies this, Repr
//            ensures length == old(length) + 1
//            ensures head != null && head.value == v
           
//         {
//             ghost var oldRepr := Repr;
//             var oldHead := head;
//             head := new Node(v,oldHead);
//             Repr := Repr + {head};
//             length := length + 1;
//         }

//     }
// }
module LinkedList{
    class Node{
        var value : int
        var next : Node?
        constructor(v:int,n:Node?)
           ensures value == v && next == n
        {
            value := v;
            next := n;
        }
    }
    class LinkedList{
        var head : Node?
        var length : nat 
        constructor()
           ensures head == null
           ensures length == 0
        {
            head := null;
            length := 0;
        }

        method Insert(v:int)
           modifies this
           ensures length == old(length) + 1
           ensures head != null && head.value == v
        {
            head := new Node(v,head);
            length := length + 1;
        }

    }
}
// 加一个 Size() 方法

// 加一个 Search() 方法

// 加一个 Remove() 方法

// 帮你逐渐加入一点点不变量（循序渐进）
