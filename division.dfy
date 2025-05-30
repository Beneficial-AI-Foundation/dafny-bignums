include "bignums.dfy"
include "modulo-integer-properties.dfy"

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
    if Compare(r, divisor) >= 0 {
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

  if divisor > dividend {
    assert quotient == 0;
    return;
  }
  QuotientIsEquivalent(dividend - divisor, divisor, quotient - 1, remainder);
  assert (dividend - divisor) / divisor == quotient - 1;
  DistributeDivision(dividend, divisor);
  assert dividend / divisor - 1 == quotient - 1;
}

lemma {:isolate_assertions} DistributeDivision(a: nat, b:nat)
  requires b != 0
  requires a - b >= 0
  ensures (a-b)/b == a/b - 1
{
  calc {
    b * ((a-b)/b);
  ==
    a-b - (a-b) % b;
  ==
    b*(a/b)-b*1 - (a-b) % b + a % b;
  ==
    //{Rearrange3(b*(a/b)-b*1, (a-b) % b, a % b);}
    b*(a/b)-b*1 + (-((a-b) % b) + a % b);
  ==
    {
      calc
      {
        -((a-b) % b) + a % b;
      ==
        (b-a) % b + a % b;
      ==
        {ModuloDistributivityAdd_int(b-a, a, b);}
        (b-a+a) % b;
      ==
        0;
      }
    }
    b*(a/b)-b*1;
  ==
    b*(a/b-1);
  }
  Cancellation(b, (a-b)/b, a/b-1);
}

// TODO Used?
lemma Rearrange3(x:int, y:int, z:int)
  ensures x - y + z == x + (-y + z)
{}

// TODO Used?
lemma InvertDivide(x:nat, y:nat)
  requires x != 0
  ensures x * (y/x) == y
{}

lemma Cancellation(x: nat, y: nat, z:nat)
  requires x != 0
  requires x*y == x*z
  ensures y == z
{

}

function Compare(a: string, b: string): int
  ensures Str2Int(a) < Str2Int(b) ==> Compare(a, b) == -1
  ensures Str2Int(a) == Str2Int(b) ==> Compare(a, b) == 0
  ensures Str2Int(a) > Str2Int(b) ==> Compare(a, b) == 1
{
  if |a| < |b| then
    -1
  else if |a| > |b| then
    1
  else
    CompareEqualLength(a, b, 0)
}

// Compare bit strings of equal length
function CompareEqualLength(a: string, b: string, i: int): int {
  if i == |a| then
    0
  else if a[i] < b[i] then
    -1
  else if a[i] > b[i] then
    1
  else
    CompareEqualLength(a, b, i+1)
}
