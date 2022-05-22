method Main()
{
    var x:int, y:int;
    assume x > 2 && y > 3;
    x := x + 1;
    y := y + x;
    assert y > 6;
}