class {:autocontracts} Stack
{
    ghost var Contents: seq<int>;
    var a: array<int>;
    var size: nat
    predicate Valid(){
        0 < a.Length
        && size <= a.Length
        && Contents == a[0..size]
    }

    constructor ()
        ensures Contents == [];
    {
        Contents := [];
        a := new int[100];
        size := 0;
    }

    method insert(e:int)
        ensures Contents == old(Contents) + [e]
    {
        size := size + 1;
        if(size > a.Length){
            var b := new int[2*size];
            forall(i | 0 < i < size){
                b[i-1] := a[i-1];
            }
            a:=b;
        }
        a[size-1] := e;
        Contents := Contents + [e];
    }

    method pop() returns(e:int)
        requires Contents != []
        ensures e == old(Contents)[old(size)-1]
        ensures Contents == old(Contents)[0..old(size)-1]
    {
        size := size - 1;
        e := a[size];
        Contents := Contents[0..size];
    }

    method peek() returns(e:int)
        requires Contents != []
        ensures e == old(Contents)[old(size)-1]
        ensures Contents == old(Contents)
    {
        return a[size-1];
    }

    method isEmpty() returns(b:bool)
        ensures b == (size == 0);
    {
        return size == 0;
    }

    method getSize() returns(n:nat)
        ensures n == size
    {
        return size;
    }

    function rev_seq(s :seq): seq
    ensures |s| == |rev_seq(s)|
    ensures forall k:nat :: 0 < k < |s| ==>  s[k] == rev_seq(s)[|s|-1-k]
    {
        if s == [] then [] else rev_seq(s[1..]) + s[0..1]
    }

    method reverse()
        ensures |Contents| == old(|Contents|)
        ensures forall k:nat :: 0 <= k < |Contents| ==> Contents[k] == old(Contents)[|Contents|-1-k]
    {
        var i:nat := 0;
        var b:array<int> := new int[a.Length];

        while(i < size)
        invariant 
        i <= size <= b.Length
        && a == old(a)
        && Contents == old(Contents)
        && Contents == a[0..size]
        && (forall k:nat :: 0 <= k < i ==> b[k] == a[size-1-k])
        && Repr == old(Repr)
        {
            b[i] := a[size-i-1];
            i:=i+1;
        }
        assert(i == size);
        assert(a in Repr);
        a := b;
        Contents := a[0..size];

        assert(0 < a.Length);
        assert(size <= a.Length);
        assert(Contents == a[0..size]);
        assert(size == old(size));
        assert(forall k:nat :: 0 <= k < |Contents| ==> Contents[k] == old(Contents)[size-1-k]);
        assert(0 < a.Length && size <= a.Length && Contents == a[0..size]);
    }

    method Main(){
        var pilha := new Stack();
        var vazia := pilha.isEmpty();
        assert vazia == true;

        pilha.insert(1);
        pilha.insert(3);
        pilha.insert(4);
        assert pilha.Contents == [1,3,4];

        var vazia2 := pilha.isEmpty();
        assert vazia2 == false;

        pilha.reverse();
        assert pilha.Contents == [4,3,1];

        var quantity := pilha.getSize();
        assert quantity == 3;
        
        var peek := pilha.peek();
        assert peek == 1;

        var pop := pilha.pop();
        assert pop == 1;
    }


}