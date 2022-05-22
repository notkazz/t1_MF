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

    predicate Valid()
      reads this, incs, decs
      //Como resolver a questão de quais objetos Celula temos acesso? Frames dinâmicos
    {
        incs != decs &&
        valor == incs.dados - decs.dados &&
        incs.dados >= 0 &&
        decs.dados >= 0
    }

    constructor ()
      ensures valor == 0
      ensures Valid()


    method Incrementa()
      requires Valid()
      ensures valor == old(valor) + 1
      ensures Valid()
    
    method Decrementa()
      requires Valid()
      ensures valor == old(valor) - 1
      ensures Valid()

    method GetValor() returns (v:int)
      requires Valid()
      ensures v == valor
      ensures Valid()
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
