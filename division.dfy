include "bignums.dfy"

method {:isolate_assertions} DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  // Initialize working variables
  var q := "";
  var r := "";

  // Long division algorithm (binary version)
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
      assert a2: OStr2Int(r) == 2 * OStr2Int(old_r) + d - OStr2Int(divisor) by {reveal OStr2Int;}
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
        OStr2Int(q) * OStr2Int(divisor) + OStr2Int(r); // TODO This is slow
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
}

lemma Rearrange2(x:nat, y:nat, z:nat, w:nat)
  ensures 2 * (x + y * z) + w == 2 * y * z + (2 * x + w)
{
}

lemma QuotientIsEquivalent(dividend : nat, divisor: nat, quotient: nat, remainder: nat)
  requires dividend == divisor * quotient + remainder
  ensures  dividend / divisor == quotient
  ensures  dividend % divisor == remainder
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
