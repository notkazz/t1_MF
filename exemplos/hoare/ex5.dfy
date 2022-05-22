method Main()
{
    var i:int;
    assume true;
    while i > 0
      //invariant true
      //decreases i
    {
        i := i-1;
    }
    assert i <= 0;
}