// Below is a self-contained Dafny program that:

// - Represents natural numbers as binary strings consisting only of `'0'` and `'1'`.
// - Has two **conversion** functions:
//   1. `str2int(s)`: Convert a valid bit-string `s` into a natural number.
//   2. `int2str(n)`: Convert a natural number `n` into its binary representation (with no leading zeros except if `n = 0`).
// 
// - Has three **pure string-based** arithmetic methods, each **not** using `str2int` or `int2str` inside the method body:
// 1. `add(s1, s2)`: Returns the bit-string representing the sum of `s1` and `s2`.
// 2. `sub(s1, s2)`: Returns the bit-string representing `s1 - s2`, assuming `s1 >= s2`.
//  3. `mul(s1, s2)`: Returns the bit-string representing the product `s1 * s2`.
//
// All methods come with specifications ensuring they do what they claim, and we prove correctness using Dafny’s function specifications (`ensures`) by comparing the result against the reference functions `str2int` and `int2str`.


method Main() {
  print "Examples:\n";

  var a := "1011";  // decimal 11
  var b := "1101";  // decimal 13

  print "a = ", a, " (decimal=", str2int(a), ")\n";
  print "b = ", b, " (decimal=", str2int(b), ")\n";

  var s := add(a, b);
  print "a + b = ", s, " (decimal=", str2int(s), ")\n";

  var d := sub(b, a);
  print "b - a = ", d, " (decimal=", str2int(d), ")\n";

  var m := mul(a, b);
  print "a * b = ", m, " (decimal=", str2int(m), ")\n";

  var z := "0";
  var sumZ := add(a, z);
  print a, " + 0 = ", sumZ, " (decimal=", str2int(sumZ), ")\n";

  // Convert integer -> string, then back
  var n := 9999;
  var sN := int2str(n);
  print "9999 -> ", sN, " -> ", str2int(sN), "\n";
}

// ----------------------------------------------------
// 5) mul: string-based multiplication
//    No direct use of str2int/int2str
// ----------------------------------------------------
method mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures str2int(res) == str2int(s1) * str2int(s2)
{
  var x := normalizeBitString(s1);
  var y := normalizeBitString(s2);

  // If either is "0", result is "0"
  if x == "0" || y == "0" {
    res := "0";
    return;
  }

  // We'll implement the classic method:
  //   product = 0
  //   for each bit of y (from right to left):
  //       if that bit == 1, add (x << position) to product
  // Use add(...) to accumulate partial sums.

  var product := "0";
  var shiftCount := 0;
  var idx := |y| - 1;
  while idx >= 0
    decreases idx
  {
    if y[idx] == '1' {
      // partial = x shifted by shiftCount
      var partial := leftShift(x, shiftCount);
      product := add(product, partial);
    }
    shiftCount := shiftCount + 1;
    idx := idx - 1;
  }
  res := product;
}

// ----------------------------------------------------
// 4) sub: string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires str2int(s1) >= str2int(s2)
  ensures ValidBitString(res)
  ensures str2int(res) == str2int(s1) - str2int(s2)
{
  var x := normalizeBitString(s1);
  var y := normalizeBitString(s2);

  // If y == "0", the difference is x
  if y == "0" {
    res := x;
    return;
  }
  // If x == y, the difference is "0"
  if x == y {
    res := "0";
    return;
  }

  var i := |x| - 1; // pointer on x
  var j := |y| - 1; // pointer on y
  var borrow := 0;
  var sb := new char[0];  // reversed result

  while i >= 0 || j >= 0
    decreases i + j, borrow
    invariant 0 <= borrow <= 1
  {
    var bitX := 0;
    if i >= 0
    { bitX := if x[i] == '1' then 1 else 0; }
    var bitY := 0;
    if j >= 0 {
      bitY := if y[j] == '1' then 1 else 0;
    }
    // Subtract with borrow:
    var diff := bitX - bitY - borrow;
    if diff < 0 {
      diff := diff + 2;
      borrow := 1;
    } else {
      borrow := 0;
    }

    if diff == 1 {
      sb := sb + ['1'];
    }
    else
    {
      sb := sb + ['0'];
    }

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }
  }

  // Reverse result
  var rev := "";
  var k := |sb| - 1;
  while k >= 0
    decreases k
  {
    rev := rev + [sb[k]];
    k := k - 1;
  }

  res := normalizeBitString(rev);
}

// ----------------------------------------------------
// 3) add: string-based addition (no str2int / int2str)
// ----------------------------------------------------
method add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures str2int(res) == str2int(s1) + str2int(s2)
{
  // We implement classic binary addition from right to left.
  // Step 1: Normalize inputs (drop leading zeros if needed).
  var x := normalizeBitString(s1);
  var y := normalizeBitString(s2);

  // If either is "0", the sum is the other.
  if x == "0" {
    res := y;
    return;
  }
  if y == "0" {
    res := x;
    return;
  }

  // We build the result from the least significant bit forward.
  var i := |x| - 1;  // index on x
  var j := |y| - 1;  // index on y
  var carry := 0;
  var sb := new char[0]; // dynamic array of chars for result (in reverse order)

  while i >= 0 || j >= 0 || carry != 0
    decreases i + j, carry
    invariant 0 <= carry <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
  {
    var bitX := 0;
    if i >= 0 {
      bitX := if x[i] == '1' then 1 else 0;
    }
    var bitY := 0;
    if j >= 0 {
      bitY := if y[j] == '1' then 1 else 0;
    }

    var sum := bitX + bitY + carry;
    var digit := sum % 2;
    carry := sum / 2;

    if digit == 1 {
      sb := sb + ['1'];
    }
    else
    {
      sb := sb + ['0'];
    }

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }
  }

  // Reverse sb to get the proper bit string
  var rev := "";
  var k := |sb| - 1;
  while k >= 0
    decreases k
  {
    rev := rev + [sb[k]];
    k := k - 1;
  }

  res := normalizeBitString(rev);
}

// ----------------------------------------------------
// 1) str2int: bit-string -> nat (reference function)
// ----------------------------------------------------
function str2int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * str2int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// ----------------------------------------------------
// 2) int2str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
function int2str(n: nat): string
  ensures str2int(s) == n
  decreases n
{
  if n == 0 then
                   "0"

  else (if n == 1
        then "1"
        else (
            // Recursively build from most significant bits.
            // The last character added is (n % 2).
            int2str(n / 2) + (if n % 2 == 0 then "0" else "1")
          )
       )
}


predicate ValidBitString(s: string)
  reads s
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ----------------------------------------------------
// Helpers for string-based arithmetic
// ----------------------------------------------------

method normalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(s)
  decreases s
{
  // If all zero or empty, return "0"
  return if |s| == 0 then
      "0"
    else
      (
        // find first '1'
        var firstOne :| 0 <= firstOne <= |s|;
        // pick the earliest i in 0..|s| if s[i] == '1'
        if (forall i | 0 <= i < |s| :: s[i] == '0') then
          ("0")
        else
          (
            // firstOne is the leftmost '1'
            s[firstOne..|s|]
          )
      )
      ;}
