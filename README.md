# dafny
method Abs(x: int) returns (x': int)
    // No precondition needed, this works for all integers.
  ensures x' >= 0 // Postcondition: The result must be non-negative.
  ensures x' == x || x' == -x // Postcondition: The result is either x or -x.
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

method FindFirstNegative(a: array?<int>) returns (index: int)
  requires a != null // Precondition: The array must not be null.
  ensures -1 <= index < a.Length // Postcondition: The index is either -1 or a valid index.
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> a[k] >= 0) // Postcondition: If -1 is returned, all elements are non-negative.
  ensures 0 <= index < a.Length ==> (a[index] < 0 && (forall k :: 0 <= k < index ==> a[k] >= 0)) // Postcondition: If a valid index is returned, it points to a negative number, and all preceding elements are non-negative.
{
  index := 0;
  while index < a.Length
    // Loop Invariant: The index 'index' is always within the bounds [0, a.Length].
    invariant 0 <= index <= a.Length
    // Loop Invariant: All elements checked so far (before 'index') are non-negative.
    invariant forall k :: 0 <= k < index ==> a[k] >= 0
    // Loop Variant (for termination): The number of elements left to check decreases.
    decreases a.Length - index
  {
    if a[index] < 0
    {
      // Found a negative number, return.
      // The postconditions will be checked here.
      return;
    }
    index := index + 1;
  }
  
  // If the loop finishes without returning, no negative number was found.
  index := -1;
  // The postconditions will be checked here as well.
}


// We define a pure 'function' for factorial to verify the 'method' against.
// This is a common pattern in Dafny.
function Factorial(n: int): int
  requires n >= 0
  decreases n // For termination checking of the recursive function
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

method ComputeFactorial(n: int) returns (f: int)
  requires n >= 0 // Precondition: Factorial is defined for non-negative integers.
  ensures f == Factorial(n) // Postcondition: The result 'f' must be equal to the mathematical factorial of n.
{
  f := 1;
  var i := 0;
  
  while i < n
    // Loop Invariant: The loop counter 'i' is between 0 and n.
    invariant 0 <= i <= n
    // Loop Invariant: 'f' holds the value of Factorial(i).
    invariant f == Factorial(i)
    // Loop Variant (for termination): The difference between n and i decreases.
    decreases n - i
  {
    i := i + 1;
    f := f * i;
  }
  // After the loop, i == n, so the invariant 'f == Factorial(i)'
  // becomes 'f == Factorial(n)', which satisfies the postcondition.
}


// Helper function to define the Tribonacci sequence, for verification.
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
  requires n >= 0 // Precondition: n must be non-negative.
  ensures t == Trib(n) // Postcondition: The result 't' is the nth Tribonacci number.
{
  if n == 0 {
    return 0; // t := 0;
  }
  if n == 1 || n == 2 {
    return 1; // t := 1;
  }
  
  // We need to establish the loop invariants before the loop.
  // Let i = 2.
  // a = Trib(i-2) = Trib(0) = 0
  // b = Trib(i-1) = Trib(1) = 1
  // c = Trib(i)   = Trib(2) = 1
  var a := 0; // Represents Trib(i-2)
  var b := 1; // Represents Trib(i-1)
  var c := 1; // Represents Trib(i)
  var i := 2; // Represents the current number for which 'c' is the Trib value.

  while i < n
    // Loop Invariant: The loop counter 'i' is between 2 and n.
    invariant 2 <= i <= n
    // Loop Invariant: 'a' holds the (i-2)th Trib number.
    invariant a == Trib(i-2)
    // Loop Invariant: 'b' holds the (i-1)th Trib number.
    invariant b == Trib(i-1)
    // Loop Invariant: 'c' holds the (i)th Trib number.
    invariant c == Trib(i)
    // Loop Variant (for termination): The difference between n and i decreases.
    decreases n - i
  {
    // Compute the next Trib number
    var next := a + b + c; // next == Trib(i-2) + Trib(i-1) + Trib(i) == Trib(i+1)
    
    // Shift the values
    a := b;     // a becomes Trib(i-1)
    b := c;     // b becomes Trib(i)
    c := next;  // c becomes Trib(i+1)
    
    // Increment the counter
    i := i + 1;
    
    // At the start of the next iteration:
    // i is now i_old + 1
    // a is Trib(i_old - 1) == Trib((i_old+1) - 2) == Trib(i-2)
    // b is Trib(i_old)     == Trib((i_old+1) - 1) == Trib(i-1)
    // c is Trib(i_old + 1) == Trib(i)
    // The invariants hold.
  }
  
  // After the loop, i == n.
  // The invariant 'c == Trib(i)' becomes 'c == Trib(n)'.
  t := c;
  // This satisfies the postcondition 'ensures t == Trib(n)'.
}
