class Nodo {
  var dado: int
  var proximo: Nodo? //a referência pode ser null, ? indica um tipo anulável

  ghost var ConteudoCauda: seq<int>
  ghost var Repr: set<object>

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (proximo != null ==> proximo in Repr && proximo.Repr <= Repr) &&
    (proximo == null ==> ConteudoCauda == []) &&
    (proximo != null ==> ConteudoCauda == [proximo.dado] + proximo.ConteudoCauda)
  }

  constructor ()
    ensures Valid() && fresh(Repr - {this})
    ensures proximo == null
  {
    proximo := null;
    ConteudoCauda := [];
    Repr := {this};
  }
}

class LinkedList
{
  var cabeca: Nodo;
  var cauda: Nodo;
  ghost var Conteudo: seq<int>
  ghost var Espinha: set<Nodo>
  ghost var Repr: set<object>

  predicate Valid()
    reads this, Repr
  {
    this in Repr && Espinha <= Repr &&
    cabeca in Espinha &&
    cauda in Espinha &&
    cauda.proximo == null &&
    (forall n :: n in Espinha ==> n.Repr <= Repr && this !in n.Repr &&
                                  n.Valid() &&
                                  (n.proximo == null ==> n == cauda)
    ) &&
    (forall n :: n in Espinha ==> n.proximo != null ==> n.proximo in Espinha) &&
    Conteudo == cabeca.ConteudoCauda
  }

  constructor ()
    ensures Valid() && fresh(Repr - {this})
    ensures |Conteudo| == 0
  {
    var n := new Nodo();
    cabeca := n;
    cauda := n;
    Conteudo := n.ConteudoCauda;
    Repr := {this} + n.Repr;
    Espinha := {n};
  }

  method EstaVazio() returns (b:bool)
    requires Valid()
    ensures b <==> |Conteudo| == 0
    ensures Conteudo == old(Conteudo)
    ensures Valid()
  {
    return cabeca == cauda;
  }

  method Cabeca() returns (e:int)
    requires Valid()
    requires |Conteudo| > 0
    ensures e == Conteudo[0]
    ensures Valid()
  {
    return cabeca.proximo.dado;
  }

  method Inserir(e:int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Conteudo == old(Conteudo) + [e]
  {
    var n := new Nodo();
    n.dado := e;
    cauda.proximo := n;
    cauda := n;
    forall m | m in Espinha
    {
      m.ConteudoCauda := m.ConteudoCauda + [e];
    }
    Conteudo := cabeca.ConteudoCauda;
    forall m | m in Espinha
    {
      m.Repr := m.Repr + n.Repr;
    }
    Repr := Repr + n.Repr;
    Espinha := Espinha + {n};
  }
}
