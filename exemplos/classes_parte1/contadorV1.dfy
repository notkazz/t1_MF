class Contador
{
    //campo
    var valor: int;

    //método
    method Incrementa()
      modifies this //indica que todos os campos podem ser modificados
      ensures valor == old(valor) + 1
    {
        valor := valor + 1;
    }

    method Decrementa()
      modifies this
      ensures valor == old(valor) - 1
    {
        valor := valor -1 ;
    }

    method GetValor() returns (v:int)
      ensures v == valor
    {
        return valor;
    }
}

method Main()
{
    var c := new Contador; //cria um novo objeto no heap
    var v := c.GetValor();
    assert v == 0; //essa asserção é falsa, pois não há inicialização com 0
    c.Incrementa();
    v := c.GetValor();
    assert v == 1;
    c.Decrementa();
    v := c.GetValor();
    assert v == 0;
}