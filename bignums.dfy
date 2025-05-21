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

// TODO Note that str2int/int2str are used in the proof inside the method bodies

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

  pow2_zero();
  assert borrow * pow2(|sb|) == 0;
  calc {
    if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0;
  ==
    str2int(x[0..i+1]) * pow2(|sb|);
  ==
    str2int(x[0..i+1]) * 1;
  ==
    str2int(x[0..i+1]);
  ==
    {assert x[0..i+1] == x;}
    str2int(x);
  }
  calc {
    if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0;
  ==
    str2int(y[0..j+1]) * pow2(|sb|);
  ==
    str2int(y[0..j+1]) * 1;
  ==
    str2int(y[0..j+1]);
  ==
    {assert y[0..j+1] == y;}
    str2int(y);
  }

  while i >= 0 || j >= 0
    decreases i + j + 2, borrow
    invariant 0 <= borrow <= 1
    invariant i <= |x| - 1 && j <= |y| - 1
    invariant i >= -1
    invariant j >= -1
    invariant ValidBitString(sb)
    invariant str2int(x) - str2int(y) ==
              str2int(sb) -
              (borrow * pow2(|sb|)) +
              (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) -
              (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0)
  {
    var old_sb := sb;
    var old_borrow := borrow;
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

    var old_i := i;
    var old_j := j;

    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }

    subAux(x, y, old_sb, sb, old_i, old_j, i, j, borrow, bitX, bitY, rawDiff, diff, old_borrow);
  }


  assert borrow == 0;


  assert str2int(x) - str2int(y) == str2int(sb);

  res := normalizeBitString(sb);

  assert str2int(sb) == str2int(res);
}

// Helper lemma for subtraction reasoning
lemma {:isolate_assertions} subAux(x: string, y: string, old_sb: string, sb: string, old_i: int,
                                   old_j: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, old_borrow:nat)
  // TODO It might be cleaner to label and selectively reveal these preconditions
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(old_sb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires old_i <= |x| - 1 && old_j <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires old_i >= 0 ==> i == old_i - 1
  requires old_j >= 0 ==> j == old_j - 1
  requires old_i < 0 ==> i == old_i
  requires old_j < 0 ==> j == old_j
  requires old_i >= 0 ==> (bitX == if x[old_i] == '1' then 1 else 0)
  requires old_j >= 0 ==> (bitY == if y[old_j] == '1' then 1 else 0)
  requires old_i < 0 ==> bitX == 0
  requires old_j < 0 ==> bitY == 0
  requires |old_sb| == |sb| - 1
  requires (if diff == 1 then ['1'] + old_sb else ['0'] + old_sb) == sb
  requires ((if old_i >= 0 then bitX else 0) - (if old_j >= 0 then bitY else 0) - old_borrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures str2int(old_sb) -
          (old_borrow * pow2(|old_sb|)) +
          (if old_i >= 0 then str2int(x[0..old_i+1]) * pow2(|old_sb|) else 0) -
          (if old_j >= 0 then str2int(y[0..old_j+1]) * pow2(|old_sb|) else 0) ==
          str2int(sb) -
          (borrow * pow2(|sb|)) +
          (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) -
          (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0)
{
  // This mirrors the structure of addAux but modified for subtraction
  var digit := 42; // TODO remove
  calc {
    str2int(old_sb) -
    (old_borrow * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i+1]) * pow2(|old_sb|) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j+1]) * pow2(|old_sb|) else 0);
  == // Apply BitStringDecomposition for both numbers
    {
      BitStringDecomposition(x, old_i);
      BitStringDecomposition(y, old_j);
    }
    str2int(old_sb) -
    (old_borrow * pow2(|old_sb|)) +
    (if old_i >= 0 then (str2int(x[0..old_i]) * 2 + bitX) * pow2(|old_sb|) else 0) -
    (if old_j >= 0 then (str2int(y[0..old_j]) * 2 + bitY) * pow2(|old_sb|) else 0);
  == // Distribute pow2(|old_sb|)
    {
      if old_i >= 0 {
        assert (str2int(x[0..old_i]) * 2 + bitX) * pow2(|old_sb|) == str2int(x[0..old_i]) * 2 * pow2(|old_sb|) + bitX * pow2(|old_sb|);
      }
      if old_j >= 0 {
        calc {
          (str2int(y[0..old_j]) * 2 + bitY) * pow2(|old_sb|);
        ==
          str2int(y[0..old_j]) * 2 * pow2(|old_sb|) + bitY * pow2(|old_sb|);
        }
      }
    }
    str2int(old_sb) -
    (old_borrow * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * 2 * pow2(|old_sb|) + bitX * pow2(|old_sb|) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * 2 * pow2(|old_sb|) + bitY * pow2(|old_sb|) else 0);
  == // Use pow2 relationship: 2 * pow2(n) = pow2(n+1)
    {
      if old_i >= 0 {
        calc {
          str2int(x[0..old_i]) * 2 * pow2(|old_sb|) + bitX * pow2(|old_sb|);
        ==
          (str2int(x[0..old_i]) * 2) * pow2(|old_sb|) + bitX * pow2(|old_sb|);
        ==
          {
            assert (str2int(x[0..old_i]) * 2) * pow2(|old_sb|) == str2int(x[0..old_i]) * (2 * pow2(|old_sb|))
            by {
              var A := str2int(x[0..old_i]);
              var B := pow2(|old_sb|);
              assert (A * 2) * B == A * (2 * B );
            }

          }
          str2int(x[0..old_i]) * (2 * pow2(|old_sb|)) + bitX * pow2(|old_sb|); // FIX
        ==
          {
            pow2_inductive(|old_sb|);
            assert pow2(|old_sb|+1) == 2 * pow2(|old_sb|);
          }
          str2int(x[0..old_i]) * pow2(|old_sb|+1) + bitX * pow2(|old_sb|);
        }
      }
      if old_j >= 0 {
        calc {
          str2int(y[0..old_j]) * 2 * pow2(|old_sb|) + bitY * pow2(|old_sb|);
        ==
          (str2int(y[0..old_j]) * 2) * pow2(|old_sb|) + bitY * pow2(|old_sb|);
        ==
          {
            assert (str2int(y[0..old_j]) * 2) * pow2(|old_sb|) == str2int(y[0..old_j]) * (2 * pow2(|old_sb|)) by {
              var A := str2int(y[0..old_j]);
              var B := pow2(|old_sb|);
              assert (A * 2) * B == A * (2 * B );
            }
          }
          str2int(y[0..old_j]) * (2 * pow2(|old_sb|)) + bitY * pow2(|old_sb|);
        ==
          {
            pow2_inductive(|old_sb|);
            assert pow2(|old_sb|+1) == 2 * pow2(|old_sb|);
          }
          str2int(y[0..old_j]) * pow2(|old_sb|+1) + bitY * pow2(|old_sb|);
        }
      }
    }
    str2int(old_sb) -
    (old_borrow * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb|+1) + bitX * pow2(|old_sb|) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb|+1) + bitY * pow2(|old_sb|) else 0);
  == // Rearrange to isolate the digit contribution
    str2int(old_sb) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb|+1) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb|+1) else 0) +
    ((if old_i >= 0 then bitX else 0) - (if old_j >= 0 then bitY else 0) - old_borrow) * pow2(|old_sb|);
  == // By the definition of diff in code
    {
      assert ((if old_i >= 0 then bitX else 0) - (if old_j >= 0 then bitY else 0) - old_borrow) == rawDiff;
    }
    str2int(old_sb) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb|+1) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb|+1) else 0) +
    (rawDiff * pow2(|old_sb|));
  == // Apply relationship between rawDiff, diff and borrow
    {
      if rawDiff < 0 {
        assert rawDiff + 2 == diff;
        assert borrow == 1;
        assert rawDiff == diff - 2;
      } else {
        assert rawDiff == diff;
        assert borrow == 0;
      }
    }
    str2int(old_sb) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb|+1) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb|+1) else 0) +
    ((if rawDiff < 0 then diff - 2 else diff) * pow2(|old_sb|));
  == // Rewrite in terms of borrow
    str2int(old_sb) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb|+1) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb|+1) else 0) +
    (diff * pow2(|old_sb|) - (if borrow == 1 then 2 * pow2(|old_sb|) else 0));
  == // Use pow2 relationship again
    {
      if borrow == 1 {
        assert 2 * pow2(|old_sb|) == pow2(|old_sb|+1) by { pow2_inductive(|old_sb|); }
      }
    }
    str2int(old_sb) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb|+1) else 0) -
    (if old_j >= 0 then str2int(y[0..old_j]) * pow2(|old_sb|+1) else 0) +
    (diff * pow2(|old_sb|) - (borrow * pow2(|old_sb|+1)));
  == // Apply PrependDigitToString
    {
      PrependDigitToString(diff, old_sb);
    }
    str2int(if diff == 1 then ['1'] + old_sb else ['0'] + old_sb) +
    (if i >= 0 then str2int(x[0..i+1]) * pow2(|old_sb|+1) else 0) -
    (if j >= 0 then str2int(y[0..j+1]) * pow2(|old_sb|+1) else 0) -
    (borrow * pow2(|old_sb|+1));
  }
}




opaque function pow2(n: nat): nat
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

  pow2_zero();
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

    addAux(x, y, old_sb, sb, old_i,
           old_j, i, j, carry, bitX, bitY, digit, sum, old_carry);


  }

  assert str2int(x) + str2int(y) == str2int(sb);

  res := normalizeBitString(sb);

  assert str2int(sb) == str2int(res);

  return res;
}

// I pulled this code out of add in the hope that Dafny would avoid timeouts
// if it was in the narrower context of a lemma. Unfortunately that didn't
// fix the timeouts, but add is easier to read with this long calculation removed.
// Annoyingly if you remove {:isolate_assertions}, this lemma sometimes times out.
// So really I need to go over it again to reduce brittleness, as in
// https://dafny.org/blog/2023/12/01/avoiding-verification-brittleness/
// I didn't check whether some of the intermediate steps can be taken out
lemma {:isolate_assertions} addAux(x: string, y: string, old_sb: string, sb: string, old_i: int,
                                   old_j: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, old_carry:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(old_sb)
  requires 0 <= carry <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires old_i <= |x| - 1 && old_j <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires old_i >= 0 ==> i == old_i - 1
  requires old_j >= 0 ==> j == old_j - 1
  requires old_i < 0 ==> i == old_i
  requires old_j < 0 ==> j == old_j
  requires old_i >= 0 ==> (bitX == if x[old_i] == '1' then 1 else 0)
  requires old_j >= 0 ==> (bitY == if y[old_j] == '1' then 1 else 0)
  requires old_i < 0 ==> bitX == 0
  requires old_j < 0 ==> bitY == 0
  requires |old_sb| == |sb| - 1
  requires sum == bitX + bitY + old_carry
  requires digit == sum % 2
  requires carry == sum / 2
  requires (if digit == 1 then ['1'] + old_sb else ['0'] + old_sb) == sb
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

  == // Start distributing pow2(|old_sb|) in the third term
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then (str2int(x[0..old_i]) * 2) * pow2(|old_sb|) + bitX * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then (str2int(y[0..old_j]) * 2 + bitY) * pow2(|old_sb|) else 0);

  == // Use associative property: (a * b) * c = a * (b * c) in the third term
    {
      if old_i >= 0 {
        assert (str2int(x[0..old_i]) * 2) * pow2(|old_sb|) == str2int(x[0..old_i]) * (2 * pow2(|old_sb|));
      }
    }
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * (2 * pow2(|old_sb|)) + bitX * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then (str2int(y[0..old_j]) * 2 + bitY) * pow2(|old_sb|) else 0);

  == // Apply identity: 2 * pow2(n) = pow2(n+1) in the third term
    {
      assert pow2(|old_sb| + 1) == 2 * pow2(|old_sb|) by {
        pow2_inductive(|old_sb|);
      }
    }
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) + bitX * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then (str2int(y[0..old_j]) * 2 + bitY) * pow2(|old_sb|) else 0);

  == // Start distributing pow2(|old_sb|) in the fourth term
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) + bitX * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then (str2int(y[0..old_j]) * 2) * pow2(|old_sb|) + bitY * pow2(|old_sb|) else 0);

  == // Use associative property in the fourth term
    {
      if old_j >= 0 {
        assert (str2int(y[0..old_j]) * 2) * pow2(|old_sb|) == str2int(y[0..old_j]) * (2 * pow2(|old_sb|));
      }
    }
    str2int(old_sb) +
    (old_carry * pow2(|old_sb|)) +
    (if old_i >= 0 then str2int(x[0..old_i]) * pow2(|old_sb| + 1) + bitX * pow2(|old_sb|) else 0) +
    (if old_j >= 0 then str2int(y[0..old_j]) * (2 * pow2(|old_sb|)) + bitY * pow2(|old_sb|) else 0);

  == // Apply identity: 2 * pow2(n) = pow2(n+1) in the fourth term
    {
      pow2_inductive(|old_sb|);
    }
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
    {
      assert old_carry + (if old_i >= 0 then bitX else 0) + (if old_j >= 0 then bitY else 0) == sum;
    }
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
    {
      calc {
        ((2 * carry + digit) * pow2(|old_sb|));
        2 * carry * pow2(|old_sb|) + digit * pow2(|old_sb|);
        {
          pow2_inductive(|old_sb|);
        }
        (digit * pow2(|old_sb|)) + (carry * pow2(|old_sb| + 1));
      }
    }
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
    {
      assert pow2(|sb|) == pow2(|old_sb| + 1);
      assert (if digit == 1 then ['1'] + old_sb else ['0'] + old_sb) == sb;
    }
    str2int(sb) +
    (carry * pow2(|sb|)) +
    (if i >= 0 then str2int(x[0..i+1]) * pow2(|sb|) else 0) +
    (if j >= 0 then str2int(y[0..j+1]) * pow2(|sb|) else 0);
  }
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


lemma ignoreInitialZeros(s : string, num_zeros:int)
  requires ValidBitString(s)
  requires 0<=num_zeros<=|s|
  requires forall i :: 0<=i<num_zeros ==> s[i] == '0'
  ensures str2int(s) == str2int(s[num_zeros..])
{
  if num_zeros == 0 {
    return;
  }
  if num_zeros == |s| {
    assert str2int(s) == (2 * str2int(s[0..|s|-1]));
    ignoreInitialZeros(s[..|s|-1], num_zeros-1);
    return;
  }
  ignoreInitialZeros(s[..|s|-1], num_zeros);
  var t := s[num_zeros..];
  calc {
    str2int(s);
  ==
    (2 * str2int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  ==
    (2 * str2int(s[num_zeros..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  ==
    {
      assert t[..|t|-1] == s[num_zeros..|s|-1];
      assert t[|t|-1] == s[|s|-1];
    }
    (2 * str2int(t[..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
  ==
    str2int(t);
  }
}

method normalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> str2int(s) == str2int(t)
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
  assert ValidBitString(s) ==> str2int(s[j..]) == str2int(s);
  while j < |validBits| && validBits[j] == '0'
    invariant j <= |validBits|
    invariant forall idx :: 0 <= idx < j ==> validBits[idx] == '0'
  {
    j := j + 1;
  }
  if ValidBitString(s){
    assert str2int(s[j..]) == str2int(s) by
    {
      ignoreInitialZeros(s, j);
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

lemma pow2_zero()
  ensures pow2(0) == 1
{
  reveal pow2();
}

lemma pow2_inductive(i: nat)
  ensures pow2(i+1) == 2*pow2(i)
{
  reveal pow2();
}

// Claude was able to mostly prove this one via calc.
// I wonder if it could be slightly easier to read by
// defining t := s[0..i+1] and expanding str2int(t)
lemma BitStringDecomposition(s: string, i: int)
  requires ValidBitString(s) && i < |s|
  ensures i >= 0 ==> str2int(s[0..i+1]) == str2int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{
  if i >= 0 {
    calc {
      str2int(s[0..i+1]);
    == // By definition of str2int
      if |s[0..i+1]| == 0 then 0
      else (2 * str2int(s[0..i+1][0..|s[0..i+1]|-1]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0));
    == // Since i >= 0, |s[0..i+1]| = i+1 > 0
      2 * str2int(s[0..i+1][0..|s[0..i+1]|-1]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    == // Simplify: s[0..i+1][0..|s[0..i+1]|-1] = s[0..i+1][0..i] = s[0..i]
      2 * str2int(s[0..i+1][0..i]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    ==
      { assert  s[0..i+1][0..i] == s[0..i];}
      2 * str2int(s[0..i]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    ==
      2 * str2int(s[0..i]) + (if s[0..i+1][i] == '1' then 1 else 0);
    == // Simplify: s[0..i+1][i] = s[i]
      2 * str2int(s[0..i]) + (if s[i] == '1' then 1 else 0);
    }
  }
}

lemma PrependDigitToString(digit: int, s: string)
  requires ValidBitString(s) && (digit == 0 || digit == 1)
  ensures str2int(if digit == 1 then ['1'] + s else ['0'] + s) ==
          str2int(s) + digit * pow2(|s|)
{
  reveal pow2();
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant str2int(if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]) == str2int(s[..i]) + digit * pow2(|s[..i]|)
  {
    var t := if digit == 1 then ['1'] + s[..i+1] else ['0'] + s[..i+1];
    calc {
      str2int(t);
    ==
      if |t| == 0 then  0  else  (2 * str2int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
    ==
      {assert |t| != 0;}
      2 * str2int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    ==
      {
        assert t[|t|-1] == s[i];
        assert t[0..|t|-1] == (if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]);
      }
      2 * str2int(if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]) + (if s[i] == '1' then 1 else 0);
    ==
      2 * (str2int(s[..i]) + digit * pow2(|s[..i]|)) + (if s[i] == '1' then 1 else 0);
    ==
      {
        var u := s[..i+1];
        calc {
          2 * str2int(s[..i]) + (if s[i] == '1' then 1 else 0);
        ==
          { assert s[..i] == u[0..|u|-1];
            assert s[i] == u[|u|-1];
          }
          2 * str2int(u[0..|u|-1]) + (if u[|u|-1] == '1' then 1 else 0);
        ==
          str2int(s[..i+1]);
        }
      }
      str2int(s[..i+1]) + digit * pow2(|s[..i+1]|);
    }

    i:= i+1;
  }
  assert s[..i] == s;
}
