method identic6(x: array<int>, n: int) returns (rez: bool)
  requires 0 <= n < x.Length
{
  var i := 0;
  rez := true;
  while i < n
    invariant 0 <= i <= n
    invariant rez ==> (forall j :: 0 <= j < i ==> x[j] == x[j + 1])
  {
    if x[i] != x[i + 1] {
      rez := false;
    }
    i := i + 1;
  }
}

method power(a: nat, p: int) returns (result: int)
  requires a != 0
  ensures result == (if p >= 0 then real_power(a, p) else 1 / real_power(a, -p))
{
  if p >= 0 {
    result := real_power(a, p);
  } else {
    result := 1 / real_power(a, -p);
  }
}

function real_power(a: nat, p: int): int
  requires p >= 0
  requires a > 0
  ensures real_power(a, p) > 0
{
  if p == 0 then 1 else a * real_power(a, p - 1)
}
