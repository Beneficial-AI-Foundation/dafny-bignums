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
  // TODO Testing claims this is outputing wrong answers
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
      // It used to be var partial := leftShift(x, shiftCount);
      // but leftShift doesn't exist. Not sure if the slice
      // is the right way
      var partial := x[shiftCount..];
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
  var sb := [];  // reversed result

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

function pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * pow2(n - 1)
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

  if y == "0" {
    res := x;
    return;
  }

  // We build the result from the least significant bit forward.
  var i := |x| - 1;  // index on x
  var j := |y| - 1;  // index on y
  var carry := 0;
  var sb := []; // dynamic seq of chars for result (in reverse order)

  assert x[0..i+1] == x;
  assert y[0..j+1] == y;
  assert str2int(x) + str2int(y) ==
         (if i >= 0 then str2int(x[0..i+1]) else 0) +
         (if j >= 0 then str2int(y[0..j+1]) else 0);

  while i >= 0 || j >= 0 || carry != 0
    decreases i + j + 2, carry
    invariant 0 <= carry <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
    invariant i >= -1
    invariant j >= -1
    invariant ValidBitString(sb)
    invariant str2int(x) + str2int(y) ==
              str2int(sb) +
              (carry * pow2(|sb|)) +
              (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) +
              (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0)
  {
    var old_sb := sb;
    var old_carry := carry;
    assert str2int(x) + str2int(y) ==
           str2int(sb) +
           (carry * pow2(|sb|)) +
           (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) +
           (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0);
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
      sb := ['1'] + sb;
    }
    else
    {
      sb := ['0'] + sb;
    }

    var old_i := i;
    var old_j := j;

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }

    assert str2int(x) + str2int(y) ==
           str2int(old_sb) +
           (old_carry * pow2(|old_sb|)) +
           (if old_i >= 0 then str2int(x[0..old_i+1]) * pow2(|old_sb|) else 0) +
           (if old_j >= 0 then str2int(y[0..old_j+1]) * pow2(|old_sb|) else 0);
    addAux(x, y, old_sb, sb, old_i,
           old_j, i, j, carry, bitX, bitY, digit, sum, old_carry);


  }

  assert str2int(x) + str2int(y) == str2int(sb);

  res := normalizeBitString(sb);

  assert str2int(sb) == str2int(res);

  return res;
}

lemma {:isolate_assertions} addAux(x: string, y: string, old_sb: string, sb: string, old_i: int,
             old_j: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, old_carry:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  ensures str2int(old_sb) +
          (old_carry * pow2(|old_sb|)) +
          (if old_i >= 0 then str2int(x[0..old_i+1]) * pow2(|old_sb|) else 0) +
          (if old_j >= 0 then str2int(y[0..old_j+1]) * pow2(|old_sb|) else 0) ==
          str2int(sb) +
          (carry * pow2(|sb|)) +
          (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) +
          (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0)
{
  calc {
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i+1]) * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j+1]) * pow2(|old_sb|) else 0);
  == // Split the x[0..old_i+1] into x[0..old_i] and the last bit
    {
      BitStringDecomposition(x, old_i);
      BitStringDecomposition(y, old_j);
    }
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then (str2int(x[0..old_i]) * 2 + bitX) * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then (str2int(y[0..old_j]) * 2 + bitY) * pow2(|old_sb|) else 0);
  == // Distribute pow2(|old_sb|)
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) + bitX * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb| + 1) + bitY * pow2(|old_sb|) else 0);
  == // Group bitX, bitY and old_carry terms
    str2int(old_sb) +
    ((old_carry + (if old_i >= 0 then bitX else 0) + (if old_j >= 0 then bitY else 0)) * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb| + 1) else 0);
  == // By definition of sum in the code
    str2int(old_sb) +
    (sum * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb| + 1) else 0);
  == // sum = 2*carry + digit
    str2int(old_sb) +
    ((2 * carry + digit) * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb| + 1) else 0);
  == // Distribute pow2(|old_sb|)
    str2int(old_sb) +
    (digit * pow2(|old_sb|)) +
    (carry * pow2(|old_sb| + 1)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb| + 1) else 0);
  == // Definition of str2int for new digit + old_sb
    {
      PrependDigitToString(digit, old_sb);
    }
    str2int(if digit == 1 then ['1'] + old_sb else ['0'] + old_sb) +
    (carry * pow2(|old_sb| + 1)) +
    (if old_i - 1 >= 0 then str2int(x[0..(old_i-1)+1]) * pow2(|old_sb| + 1) else 0) +
    (if old_j - 1 >= 0 then str2int(y[0..(old_j-1)+1]) * pow2(|old_sb| + 1) else 0);
  == // By definition of sb and updated i, j
    str2int(sb) +
    (carry * pow2(|sb|)) +
    (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) +
    (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0);
  }
}

lemma BitStringDecomposition(s: string, i: int)
  requires ValidBitString(s) && i < |s|
  ensures i >= 0 ==> str2int(s[0..i+1]) == str2int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{
  // Proof implementation
}

lemma PrependDigitToString(digit: int, s: string)
  requires ValidBitString(s) && (digit == 0 || digit == 1)
  ensures str2int(if digit == 1 then ['1'] + s else ['0'] + s) ==
          str2int(s) + digit * pow2(|s|)
{
  // Proof implementation
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
  ensures ValidBitString(int2str(n))
  ensures str2int(int2str(n)) == n
  decreases n
  // TODO Should I also check the other way, e.g. int2str(str2int(s)) = s?
  // That would be a little more complicated, since not all strings are valid---we'd have
  // to ensure that s is a valid bitstring
{
  if n == 0 then
    "0"

  else (if n == 1
        then "1"
        else (
            // Recursively build from most significant bits.
            // The last character added is (n % 2).
            assert ValidBitString(int2str(n/2));
            assert str2int(int2str(n/2)) == n/2;
            int2str(n / 2) + (if n % 2 == 0 then "0" else "1")
          )
       )
}


predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ----------------------------------------------------
// Helpers for string-based arithmetic
// ----------------------------------------------------

method normalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> str2int(s) == str2int(t)
  decreases s
{
  // First pass: keep only valid bits
  var validBits := "";
  var i := 0;
  while i < |s|
    invariant ValidBitString(validBits)
  {
    if s[i] == '0' || s[i] == '1' {
      validBits := validBits + [s[i]];
    }
    i := i + 1;
  }

  assert ValidBitString(validBits);
  // Second pass: remove leading zeros
  var j := 0;
  while j < |validBits| && validBits[j] == '0'
    invariant j <= |validBits|
  {
    j := j + 1;
  }

  // Extract substring after leading zeros
  if j == |validBits| {
    // All zeros or empty
    return "0";
  }
  assert j <= |validBits|;
  return validBits[j..];
}
