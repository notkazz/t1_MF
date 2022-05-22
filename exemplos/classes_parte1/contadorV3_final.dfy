class Celula
{
    var dados: int;
    constructor ()
      ensures dados == 0
    {
        dados := 0;
    }
}

class Contador
{
    //Contador é representado pelo número
    //de operações de incremento e decremento
    //armazenadas em um objeto Celula
    var incs: Celula;
    var decs: Celula;
    //valor é uma representação abstrata
    ghost var valor: int;
    //Controle de frames dinâmicos
    //Repr é a coleção de objetos que representam a classe sendo implementada
    //Nesse caso serão this, incs e decs 
    ghost var Repr: set<object>;

    predicate Valid()
      reads this, Repr
    {
        this in Repr &&
        incs in Repr &&
        decs in Repr &&
        incs != decs &&
        valor == incs.dados - decs.dados &&
        incs.dados >= 0 &&
        decs.dados >= 0
    }

    constructor ()
      ensures valor == 0
      ensures Valid()
      ensures fresh(Repr - {this})
    {
        incs := new Celula();
        decs := new Celula();
        valor := 0;
        Repr := {this, incs, decs};
    }

    method Incrementa()
      requires Valid()
      modifies Repr
      ensures valor == old(valor) + 1
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
        incs.dados := incs.dados + 1;
        valor := valor + 1;
    }
    
    method Decrementa()
      requires Valid()
      modifies Repr
      ensures valor == old(valor) - 1
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
        decs.dados := decs.dados + 1;
        valor := valor - 1;
    }

    method GetValor() returns (v:int)
      requires Valid()
      ensures v == valor
      ensures Valid()
    {
        v := incs.dados - decs.dados;
    }
}

method Main()
{
    var c := new Contador();
    c.Incrementa();
    c.Incrementa();
    c.Decrementa();
    c.Incrementa();
    assert c.valor == 2;
}