class {:autocontracts}  Pilha
{
    //Implementação
    var a: array<int>;
    var b: array<int>;
    var header: nat;
    var isEmpty: bool;
    //Abstração
    ghost var Conteudo: seq<int>;

    predicate Valid()
    {
        (!isEmpty ==> header == a.Length - 1 && Conteudo == a[0..header])
        && isEmpty ==> Conteudo == []
    }

    constructor()
        ensures Conteudo == []
        ensures header == 0
    {
        isEmpty := true;
        header := 0;
        a := new int[1];
        Conteudo := [];
    }

    method Empilha(e:int)
        requires a.Length >= 1
        ensures old(isEmpty) ==> isEmpty == false
        ensures Conteudo == old(Conteudo) + [e]
        ensures header == |Conteudo| - 1
        
        modifies a
    {

        if isEmpty{
            header := 0;
        } else {
            header := header+1;
        }

        if (header >= a.Length-1){
            b := new int[a.Length*2];
            
            forall i | 0 <= i < a.Length
            {
                b[i] := a[i];
            }
            a := b;
            
        }

        a[header] := e;
        Conteudo := Conteudo + [e];
        isEmpty := false;


    }

    method Despilha()
    {

    }




    method Main()
    {
        var pilha := new Pilha();

    }
    
}