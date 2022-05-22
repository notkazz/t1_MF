method Main()
{
    var x:int;
    assume true;
    if x < 0
    {
        x := -x;
    }
    assert x >= 0;
}