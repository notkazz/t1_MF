function Fact(n:nat):nat
{
    if n == 0
    then 1
    else n * Fact(n-1)
}

method Main()
{
    var n:nat, i:nat, f:nat;
    assume n >= 0;
    f := 1;
    i := 1;
    while i <= n
      invariant i - 1 <= n
      invariant f == Fact(i-1)
    {
        f := f * i;
        i := i + 1;
    }
    assert f == Fact(n);
}