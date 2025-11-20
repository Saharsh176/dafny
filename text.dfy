// LOGIC ASSIGNMENT 2

//TASK 1
method Abs(x: int) returns (x': int)
  ensures x' >= 0
  ensures x' == x || x' == -x
{
  if x < 0
  {
    x' := -x;
  }
  else
  {
    x' := x;
  }
}

//TASK 2

method FindFirstNegative(a: array?<int>) returns (index: int)
  requires a != null
  ensures -1 <= index < a.Length
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> a[k] >= 0)
  ensures 0 <= index < a.Length ==> (a[index] < 0 && (forall k :: 0 <= k < index ==> a[k] >= 0))
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] >= 0
    decreases a.Length - index
  {
    if a[index] < 0
    {
      return;
    }
    index := index + 1;
  }
  
  index := -1;
}

//TASK 3

function Factorial(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

method ComputeFactorial(n: int) returns (f: int)
  requires n >= 0
  ensures f == Factorial(n)
{
  f := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant f == Factorial(i)
    decreases n - i
  {
    i := i + 1;
    f := f * i;
  }
}

//TASK 4

function Trib(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else if n == 2 then 1
  else Trib(n-1) + Trib(n-2) + Trib(n-3)
}

method ComputeTribonacci(n: int) returns (t: int)
  requires n >= 0
  ensures t == Trib(n)
{
  if n == 0 {
    return 0;
  }
  if n == 1 || n == 2 {
    return 1;
  }
  
  var a := 0;
  var b := 1;
  var c := 1;
  var i := 2;

  while i < n
    invariant 2 <= i <= n
    invariant a == Trib(i-2)
    invariant b == Trib(i-1)
    invariant c == Trib(i)
    decreases n - i
  {
    var next := a + b + c;
    
    a := b;
    b := c;
    c := next;
    
    i := i + 1;
  }
  
  t := c;
}
