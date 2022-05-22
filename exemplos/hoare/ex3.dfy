method Main()
{
    var x:int , y:int , z:int , x0:int , y0:int;
    assume x == x0 && y == y0;
    if (x > y)
    {
        z := y;
        y := x;
        x := z;
    }
    assert x <= y &&  ((x == x0 && y == y0) || (x == y0 && y == x0));
}