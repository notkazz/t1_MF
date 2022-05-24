class {:autocontracts}  Pilha
{
    //Implementação
    var a: array<int>;
    var header: nat;
    var empty: bool;
    var amount: nat;
    //Abstração
    ghost var Conteudo: seq<int>;

    predicate Valid()
    {
        header < a.Length-1
        &&(!empty ==> Conteudo == a[0..header])
        &&(|Conteudo| == header+1)
        &&(!empty ==> amount>0)
        && empty ==> Conteudo == []
    }

    constructor()
        ensures Conteudo == []
        ensures header == 0
        ensures header < a.Length - 1
        ensures empty
    {
        empty := true;
        header := 0;
        a := new int[10];
        amount := 0;
        Conteudo := [];

    }

    method Empilha(e:int)
        requires header < a.Length-1
        requires header == |Conteudo|-1
        requires Conteudo == a[0..header]
        ensures empty == false
        ensures header < a.Length-1
        ensures old(!empty) ==> old(header)+1 == header
        ensures header == |Conteudo|-1
    {

        if(!empty){
            assert((!empty ==> Conteudo == a[0..header]));
            header := header+1;
        }
        empty := false;
        amount := amount + 1;
        a[header] := e;
        Conteudo := Conteudo + [e];

        if(header == a.Length-1){
            var b:array<int> := new int[a.Length * 2];
            var i:nat := 0;
            while(i < a.Length)
            invariant a.Length < b.Length
            && header == a.Length-1 
            && empty == false
            {
                b[i] := a[i];
                i:= i+1;
            }
            a:=b;
        }

    }


    method Peek() returns (val:int)
    requires header == |Conteudo|-1
    requires !empty
    requires header < a.Length-1
    ensures header < a.Length -1
    ensures a[header] == old(a[header])
    ensures header == |Conteudo|-1
    {
        return a[header];
    }

    method Pop() returns (val:int)
    requires header == |Conteudo|-1
    requires header < a.Length-1
    requires !empty && amount>0;
    requires |Conteudo| == header+1;
    ensures old(header) == 0 ==> empty
    ensures old(header)>0 ==> old(header)-1 == header
    ensures old(!empty) ==> header < a.Length-1
    ensures header == |Conteudo|-1 || empty
    {
        val := a[header];
        if(header == 0){
            empty := true;
            Conteudo := [];
        }else{
            header := header-1;
            Conteudo := Conteudo[0..header];
        }
        amount := amount - 1;
        return val;
    }

    method isEmpty() returns (b:bool)
    requires header == |Conteudo|-1
    requires header < a.Length-1
    ensures b == empty
    ensures header < a.Length-1
    ensures header == |Conteudo|-1
    {
        return empty;
    }

    method howMany() returns (n:nat)
    requires header == |Conteudo|-1
    requires header < a.Length-1
    ensures n == amount
    ensures header < a.Length-1
    ensures header == |Conteudo|-1
    {
        return amount;
    }

    method reverse()
    requires header == |Conteudo|-1
    requires header < a.Length-1
    requires |Conteudo| == a.Length
    requires a.Length > 0
    requires Conteudo == a[0..header]
    ensures header < a.Length-1
    ensures header == |Conteudo|-1
    {
        ghost var Conteudo2: seq<int> := [];
        var i := 1;
        var b:array<int> := new int[a.Length];

        while(i <= header)
        invariant a.Length == b.Length 
        && a.Length == |Conteudo|
        && header < b.Length - 1
        {
            Conteudo2 := Conteudo2 + [Conteudo[|Conteudo|-i-1]];
            b[i-1] := a[i-1];
            i := i+1;
        }
        a:=b;
        Conteudo := Conteudo2;
    }


    method Main()
    {
        var pilha := new Pilha();
        assert pilha.empty;
        var vazia := pilha.isEmpty();
        assert vazia == true;

        pilha.Empilha(1);
        pilha.Empilha(3);
        pilha.Empilha(4);
        assert pilha.Conteudo == [1,3,4];

        var vazia2 := pilha.isEmpty();
        assert vazia2 == false;

        pilha.reverse();
        assert pilha.Conteudo == [4,3,1];

        var quantity := pilha.howMany();
        assert quantity == 3;
        
        var peek := pilha.Peek();
        assert peek == 1;

        var pop := pilha.Pop();
        assert pop == 1;


    }
    
}