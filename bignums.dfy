include "bignums-lemmas.dfy"
include "sub-aux.dfy"
include "add-aux.dfy"
include "mul-aux.dfy"
// Below is a Dafny program that:

// - Represents natural numbers as binary strings consisting only of `'0'` and `'1'`.
// - Has two **conversion** functions:
//   1. `Str2Int(s)`: Convert a valid bit-string `s` into a natural number.
//   2. `Int2Str(n)`: Convert a natural number `n` into its binary representation (with no leading zeros except if `n = 0`).
//
// - Has three **pure string-based** arithmetic methods, each **not** using `Str2Int` or `Int2Str` inside the method body:
// 1. `Add(s1, s2)`: Returns the bit-string representing the sum of `s1` and `s2`.
// 2. `Sub(s1, s2)`: Returns the bit-string representing `s1 - s2`, assuming `s1 >= s2`.
//  3. `Mul(s1, s2)`: Returns the bit-string representing the product `s1 * s2`.
//
// All methods come with specifications ensuring they do what they claim, and we prove correctness using Dafny's function specifications (`ensures`) by comparing the result against the reference functions `Str2Int` and `Int2Str`.

// Note: To check that Add/Sub/Mul only use Int2Str and Str2Int for verification:
// 1. Change Int2Str, OStr2Int, and Str2Int to `ghost function`
// 2. Delete Main (because it uses Int2Str/Str2Int in executable code, so now won't verify)
// 3. The rest of the code will still verify


// ----------------------------------------------------
// Int2Str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
function Int2Str(n: nat): string
  // I added the following post-condition because Str2Int requires it
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    "0"

  else (if n == 1
        then "1"
        else (
            // Recursively build from most significant bits.
            // The last character added is (n % 2).
            assert ValidBitString(Int2Str(n/2));
            assert Str2Int(Int2Str(n/2)) == n/2;
            Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
          )
       )
}


method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  // First pass: keep only valid bits
  var validBits := "";
  var i := 0;
  while i < |s|
    invariant ValidBitString(validBits)
    invariant 0 <= i <= |s|
    invariant i >= |validBits|
    invariant |s| >= |validBits|
    invariant ValidBitString(s) ==> i == |validBits|
    invariant ValidBitString(s) ==> s[..i] == validBits[..i]
  {
    if s[i] == '0' || s[i] == '1' {
      validBits := validBits + [s[i]];
    }
    i := i + 1;
  }
  assert ValidBitString(s) ==> s == validBits;
  assert ValidBitString(validBits);
  // Second pass: remove leading zeros
  var j := 0;
  assert ValidBitString(s) ==> Str2Int(s[j..]) == Str2Int(s);
  while j < |validBits| && validBits[j] == '0'
    invariant j <= |validBits|
    invariant forall idx :: 0 <= idx < j ==> validBits[idx] == '0'
  {
    j := j + 1;
  }
  if ValidBitString(s){
    assert Str2Int(s[j..]) == Str2Int(s) by
    {
      IgnoreInitialZeros(s, j);
    }
  }

  // Extract substring after leading zeros
  if j == |validBits| {
    // All zeros or empty
    return "0";
  }
  assert j <= |validBits|;
  return validBits[j..];
}


// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // We implement classic binary addition from right to left.
  // Step 1: Normalize inputs (drop leading zeros if needed).
  var x := NormalizeBitString(s1);
  var y := NormalizeBitString(s2);

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
  assert Str2Int(x) + Str2Int(y) ==
         (if i >= 0 then Str2Int(x[0..i+1]) else 0) +
         (if j >= 0 then Str2Int(y[0..j+1]) else 0);

  Pow2Zero();
  while i >= 0 || j >= 0 || carry != 0
    decreases i + j + 2, carry
    invariant 0 <= carry <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
    invariant i >= -1
    invariant j >= -1
    invariant ValidBitString(sb)
    invariant Str2Int(x) + Str2Int(y) ==
              Str2Int(sb) +
              (carry * Pow2(|sb|)) +
              (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
              (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
  {
    var oldSb := sb;
    var oldCarry := carry;
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

    var oldI := i;
    var oldJ := j;

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }

    AddAuxTop(x, y, oldSb, sb, oldI,
              oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  }

  assert Str2Int(x) + Str2Int(y) == Str2Int(sb);

  res := NormalizeBitString(sb);

  assert Str2Int(sb) == Str2Int(res);

  return res;
}


// ----------------------------------------------------
// string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var x := NormalizeBitString(s1);
  var y := NormalizeBitString(s2);

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
  var sb := [];

  Pow2Zero();
  assert borrow * Pow2(|sb|) == 0;
  calc {
    if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0;
  ==
    Str2Int(x[0..i+1]) * Pow2(|sb|);
  ==
    Str2Int(x[0..i+1]) * 1;
  ==
    Str2Int(x[0..i+1]);
  ==
    {assert x[0..i+1] == x;}
    Str2Int(x);
  }
  calc {
    if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0;
  ==
    Str2Int(y[0..j+1]) * Pow2(|sb|);
  ==
    Str2Int(y[0..j+1]) * 1;
  ==
    Str2Int(y[0..j+1]);
  ==
    {assert y[0..j+1] == y;}
    Str2Int(y);
  }

  while i >= 0 || j >= 0
    decreases i + j + 2, borrow
    invariant 0 <= borrow <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
    invariant i >= -1
    invariant j >= -1
    invariant ValidBitString(sb)
    invariant Str2Int(x) - Str2Int(y) ==
              Str2Int(sb) -
              (borrow * Pow2(|sb|)) +
              (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) -
              (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
  {
    var oldSb := sb;
    var oldBorrow := borrow;
    var bitX := 0;
    if i >= 0 {
      bitX := if x[i] == '1' then 1 else 0;
    }
    var bitY := 0;
    if j >= 0 {
      bitY := if y[j] == '1' then 1 else 0;
    }

    // Subtract with borrow:
    var rawDiff := bitX - bitY - borrow;
    var diff := rawDiff;
    if rawDiff < 0 {
      diff := rawDiff + 2;
      borrow := 1;
    } else {
      borrow := 0;
    }

    assert diff == 1 || diff == 0;
    if diff == 1 {
      sb := ['1'] + sb;
    } else {
      sb := ['0'] + sb;
    }

    var oldI := i;
    var oldJ := j;

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }

    SubAuxTop(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
    reveal OStr2Int;
  }



  // If borrow is 1, the RHS will be negative,
  // but the LHS is nonnegative
  assert Str2Int(x) - Str2Int(y) == Str2Int(sb) - (borrow * Pow2(|sb|));
  assert Pow2(|sb|) > Str2Int(sb) by {Bound(sb);}
  assert borrow == 0;


  assert Str2Int(x) - Str2Int(y) == Str2Int(sb);

  res := NormalizeBitString(sb);

  assert Str2Int(sb) == Str2Int(res);
}



// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  var x := NormalizeBitString(s1);
  var y := NormalizeBitString(s2);

  // If either is "0", result is "0"
  if x == "0" || y == "0" {
    res := "0";
    return;
  }

  // We'll implement the classic method:
  //   product = 0
  //   for each bit of y (from right to left):
  //       if that bit == 1, add (x << position) to product
  // Use Add(...) to accumulate partial sums.

  var product := "0";
  var shift := "";
  var idx := |y| - 1;
  calc {
    OStr2Int(x) * OStr2Int(y);
  ==
    {
      assert OStr2Int(product) == 0 by {reveal OStr2Int;}
      assert y[..idx+1] + shift == y;
      assert OStr2Int(y[..idx+1] + shift) == OStr2Int(y);
    }
    OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
  }
  while idx >= 0
    decreases idx
    invariant -1 <= idx < |y|
    invariant ValidBitString(y[..idx+1] + shift)
    invariant ValidBitString(product)
    invariant ValidBitString(shift)
    invariant forall i :: 0<=i<|shift| ==> shift[i] == '0'
    invariant OStr2Int(x) * OStr2Int(y) == OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift)
  {
    var prevProduct := product;
    var prevIdx := idx;
    var prevShift := shift;
    if y[idx] == '1' {
      var partial := x + shift;
      product := Add(product, partial);
      assert OStr2Int(product) == OStr2Int(prevProduct)+ OStr2Int(x + prevShift) by {reveal OStr2Int;}
    }
    shift := shift + ['0'];
    idx := idx - 1;
    assert ValidBitString(y[..idx+1] + shift);

    // Use the MulAux lemma to maintain the loop invariant
    MulAux(x, y, prevProduct, product, prevShift, shift, idx);
  }
  assert idx == -1;
  calc {
    OStr2Int(x) * OStr2Int(y);
  ==
    OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
  ==
    { assert y[..idx+1] == "";
      assert y[..idx+1] + shift == shift;
    }
    OStr2Int(product) + OStr2Int(x) * OStr2Int(shift);
  ==
    {reveal OStr2Int;
     IgnoreInitialZeros(shift, |shift|);}
    OStr2Int(product);
  }
  assert Str2Int(x) * Str2Int(y) == Str2Int(product) by {reveal OStr2Int;}
  res := product;
}



method Main() {
  print "Examples:\n";

  var a := "1011";  // decimal 11

  var b := "1101";  // decimal 13

  print "a = ", a, " (decimal=", Str2Int(a), ")\n";
  print "b = ", b, " (decimal=", Str2Int(b), ")\n";

  var s := Add(a, b);
  print "a + b = ", s, " (decimal=", Str2Int(s), ")\n";

  // sub needs to know that the result will be positive
  Eleven();
  Thirteen();
  var d := Sub(b, a);
  print "b - a = ", d, " (decimal=", Str2Int(d), ")\n";

  var m := Mul(a, b);
  print "a * b = ", m, " (decimal=", Str2Int(m), ")\n";

  var z := "0";
  var sumZ := Add(a, z);
  print a, " + 0 = ", sumZ, " (decimal=", Str2Int(sumZ), ")\n";

  // Convert integer -> string, then back
  var n := 9999;
  var sN := Int2Str(n);
  print "9999 -> ", sN, " -> ", Str2Int(sN), "\n";
}
