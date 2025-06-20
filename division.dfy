include "bignums.dfy"
include "bound.dfy"

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  // Initialize working variables
  var q := "";
  var r := "";

  assert OStr2Int(r) < OStr2Int(divisor) by {reveal OStr2Int;}
  assert OStr2Int(dividend[..0]) == OStr2Int(r) + OStr2Int(q) * OStr2Int(divisor) by {reveal OStr2Int;}
  // See section 4.3.1 of The Art of Computer Programming, Volume 2.
  // i.e. PDF page 284 of
  // https://github.com/manjunath5496/The-Art-of-Computer-Programming-Books/blob/master/aoc(6).pdf
  // Except because the base is 2, we can find the next quotient digit by comparing r to the divisor,
  // instead of guessing and checking
  for i := 0 to |dividend|
    invariant ValidBitString(r)
    invariant ValidBitString(q)
    invariant OStr2Int(dividend[..i]) == OStr2Int(r) + OStr2Int(q) * OStr2Int(divisor)
    invariant OStr2Int(r) < OStr2Int(divisor)
  {
    // Shift remainder left and bring down next bit
    ghost var old_r := r;
    ghost var old_q := q;
    r := r + [dividend[i]];
    assert ValidBitString(r);
    ghost var d := if dividend[i] == '1' then 1 else 0;
    assert a1 : OStr2Int(r) == 2 * OStr2Int(old_r) + d by {reveal OStr2Int;}

    calc {
      OStr2Int(dividend[..i + 1]);
    ==
      {assert dividend[..i + 1][..|dividend[..i + 1]| -1 ] == dividend[..i];
       reveal OStr2Int;}
      2 * OStr2Int(dividend[..i]) + d;
    ==
      2 * (OStr2Int(old_r) + OStr2Int(old_q) * OStr2Int(divisor)) + d;
    ==
      {Rearrange2(OStr2Int(old_r), OStr2Int(old_q), OStr2Int(divisor),d);}
      2 * OStr2Int(old_q) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d);
    }

    // Check if divisor can be subtracted from current remainder
    var comparison := Compare(r, divisor);
    if comparison >= 0 {
      // Subtract divisor from remainder
      r := Sub(r, divisor);
      assert OStr2Int(r) < OStr2Int(divisor) by {reveal OStr2Int;}
      assert ValidBitString(r);
      assert a2: OStr2Int(r) == 2 * OStr2Int(old_r) + d - OStr2Int(divisor) by {reveal a1; reveal OStr2Int;}
      q := q + "1";
      assert ValidBitString(q);
      assert a3 : OStr2Int(q) == 2 * OStr2Int(old_q) + 1 by {reveal OStr2Int;}
      calc {
        2 * OStr2Int(old_q) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d);
      ==
        (2 * OStr2Int(old_q) + 1) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d - OStr2Int(divisor));
      ==
        {
          reveal a2;
          reveal a3;
        }
        OStr2Int(q) * OStr2Int(divisor) + OStr2Int(r);
      }
    } else {
      assert ValidBitString(r);
      assert OStr2Int(r) < OStr2Int(divisor) by {reveal OStr2Int;}
      q := q + "0";
      assert ValidBitString(q);
      assert OStr2Int(q) == 2 * OStr2Int(old_q) by {reveal OStr2Int;}
      calc {
        2 * OStr2Int(old_q) * OStr2Int(divisor) + (2 * OStr2Int(old_r) + d);
      ==
        {reveal OStr2Int;}
        OStr2Int(q) * OStr2Int(divisor) + OStr2Int(r);
      }
    }

  }
  calc {
    OStr2Int(dividend);
  ==
    {assert dividend[..|dividend|] == dividend;}
    OStr2Int(dividend[..|dividend|]);
  ==
    OStr2Int(r) + OStr2Int(q) * OStr2Int(divisor);
  }
  assert OStr2Int(r) < OStr2Int(divisor);

  quotient := q;
  remainder := r;
  QuotientIsEquivalent(OStr2Int(dividend), OStr2Int(divisor), OStr2Int(quotient), OStr2Int(remainder));
  assert Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor) by {reveal OStr2Int;}
  assert Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor) by {reveal OStr2Int;}
}

lemma Rearrange2(x:nat, y:nat, z:nat, w:nat)
  ensures 2 * (x + y * z) + w == 2 * y * z + (2 * x + w)
{
}

lemma QuotientIsEquivalent(dividend : nat, divisor: nat, quotient: nat, remainder: nat)
  requires dividend == divisor * quotient + remainder
  requires remainder < divisor
  requires divisor != 0
  ensures  dividend / divisor == quotient
  ensures  dividend % divisor == remainder
{
  assert (dividend / divisor) * divisor + dividend % divisor == dividend;
  assert (quotient - (dividend / divisor)) * divisor == dividend % divisor - remainder;
  Bounding(dividend % divisor - remainder, divisor, quotient - (dividend / divisor));
}




method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  // First normalize both strings
  var a := NormalizeBitString(s1);
  var b := NormalizeBitString(s2);

  // Compare lengths first
  if |a| < |b| {
    var res':= CompareUnequal(b, a);
    res := -res';
    return;
  }
  if |a| > |b| {
    res:= CompareUnequal(a, b);
    return;
  }

  // Equal lengths - compare bits from most significant
  if |a| == 0 {
    return 0;
  }

  // Recursive case - compare first bits then recurse on tails
  if a[0] < b[0] {
    return -1;
  }
  if a[0] > b[0] {
    return 1;
  }
  if a == "0" {
    return 0;
  }

  // First bits equal, compare rest
  assert a[0] == b[0];
  assert a[0] == '1';
  assert b[0] == '1';

  calc {
    Pow2(|b[1..]|) + Str2Int(b[1..]);
  ==
    {PrependDigitToString(1, b[1..]);}
    Str2Int(['1'] + b[1..]);
  ==
    {assert ['1'] + b[1..] == b;}
    Str2Int(b);
  }
  calc {
    Pow2(|a[1..]|) + Str2Int(a[1..]);
  ==
    {PrependDigitToString(1, a[1..]);}
    Str2Int(['1'] + a[1..]);
  ==
    {assert ['1'] + a[1..] == a;}
    Str2Int(a);
  }
  assert Str2Int(a) > Str2Int(a[1..]) by {
    Pow2Positive(|a[1..]|);
  }
  assert Str2Int(b) > Str2Int(b[1..]) by {
    Pow2Positive(|b[1..]|);
  }
  res := Compare(a[1..], b[1..]);
}

method CompareUnequal(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  requires |s1| > 0
  requires |s1| > 1 ==> s1[0] != '0'
  requires |s2| > 0
  requires |s2| > 1 ==> s2[0] != '0'
  requires |s1| > |s2|
{
  var a := s1;
  var b := s2;

  // Split a into head and tail
  var head := a[0];
  var tail := a[1..];

  // Since a is normalized and longer than b, its first bit must be 1
  assert head == '1';
  calc {
    Pow2(|tail|) + Str2Int(tail);
  ==
    {PrependDigitToString(1, tail);}
    Str2Int(['1'] + tail);
  ==
    {assert ['1'] + tail == a;}
    Str2Int(a);
  }

  // The tail's value is bounded
  assert Str2Int(tail) < Pow2(|tail|) by {
    Bound(tail);
  }

  // b's value is bounded
  assert Str2Int(b) < Pow2(|b|) by {
    Bound(b);
  }

  // Since |b| < |a|, b's bound is smaller
  assert Pow2(|b|) <= Pow2(|a|-1) by {assert |b| <= |a|-1;
                                      Pow2Monotonic(|b|, |a|-1);}

  // Therefore a > b
  calc {
    Str2Int(a);
  ==
    Pow2(|a|-1) + Str2Int(tail);
  >=
    Pow2(|a|-1);
  >=
    Pow2(|b|);
  >
    Str2Int(b);
  }

  return 1;
}
