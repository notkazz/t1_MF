class Contador
{
    //Contador é representado pelo número
    //de operações de incremento e decremento
    //Implementação concreta deve ficar "invisível" nos contratos
    var incs: int;
    var decs: int;
    //valor é uma representação abstrata
    //o contrato público dos métodos somente pode referenciar "valor"
    ghost var valor: int;

    //Invariante de classe
    predicate Valid()
    reads this
    {
        valor == incs - decs
        && incs >= 0
        && decs >= 0
    }

    constructor ()
    ensures Valid()
    ensures valor == 0
    {
        incs := 0;
        decs := 0;
        valor := 0;
    }

    method incrementa()
    requires Valid()
    modifies this
    ensures Valid()
    ensures valor == old(valor) + 1
    {
        incs := incs + 1;
        valor := valor + 1;
    }

    method decrementa()
    requires Valid()
    modifies this
    ensures Valid()
    ensures valor == old(valor) - 1
    {
        decs := decs + 1;
        valor := valor - 1;
    }

    method getValor() returns (v:int)
    requires Valid()
    ensures v == valor
    ensures Valid()
    {
        return incs - decs;
    }
}

method Main()
{
    var c := new Contador();
    var v := c.getValor();
    assert v == 0;
    c.incrementa();
    var v2 := c.getValor();
    assert v2 == 1;
}