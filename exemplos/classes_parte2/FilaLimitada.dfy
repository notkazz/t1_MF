class {:autocontracts}  FilaNat
{
    //Implementação
    var a: array<nat>;
    var cauda: nat;
    const max: nat;
    //Abstração
    ghost var Conteudo: seq<nat>;
    ghost const TamanhoMaximo: nat;

    //Invariante de classe
    predicate Valid()
    {
        max > 0
        && a.Length == max
        && 0 <= cauda <= max
        && Conteudo == a[0..cauda]
        && TamanhoMaximo == max
    }

    constructor (m:nat)
      requires m > 0
      ensures TamanhoMaximo == m
      ensures Conteudo == []
    {
        max := m;
        a := new nat[m];
        cauda := 0;
        Conteudo := [];
        TamanhoMaximo := max;
    }

    method QuantidadeMaxima() returns (n:nat)
      ensures n == TamanhoMaximo
      ensures Conteudo == old(Conteudo)
    {
        return max;
    }

    method Quantidade() returns (n:nat)
      ensures n == |Conteudo|
      ensures Conteudo == old(Conteudo)
    {
        return cauda;
    }

    method Enfileira(e:nat)
      requires |Conteudo| < TamanhoMaximo
      ensures Conteudo == old(Conteudo) + [e]
    {
        a[cauda] := e;
        cauda := cauda + 1;
        Conteudo := Conteudo + [e];
    }

    method Desenfileira() returns (e:nat)
      requires |Conteudo| > 0
      ensures e == old(Conteudo)[0]
      ensures Conteudo == old(Conteudo)[1..]
    {
        e := a[0];
        cauda := cauda - 1;
        forall i | 0 <= i < cauda
        {
            a[i] := a[i+1];
        }
        Conteudo := a[0..cauda];
    }
}

method Main()
{
    var fila := new FilaNat(5);
    fila.Enfileira(1);
    fila.Enfileira(2);
    assert fila.Conteudo == [1,2];
    var q := fila.Quantidade();
    assert q == 2;
    var e := fila.Desenfileira();
    assert e == 1;
    assert fila.Conteudo == [2];
}










