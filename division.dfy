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
    invariant Str2Int(dividend[..i]) == Str2Int(r) + Str2Int(q) * Str2Int(divisor)
  {
    // Shift remainder left and bring down next bit
    ghost var old_r := r;
    ghost var old_q := q;
    r := r + [dividend[i]];
    ghost var d := if dividend[i] == '1' then 1 else 0;
    assert a1 : Str2Int(r) == 2 * Str2Int(old_r) + d;

    // Check if divisor can be subtracted from current remainder
    if Compare(r, divisor) >= 0 {
      // Subtract divisor from remainder
      r := Sub(r, divisor);
      q := q + "1";
      assert Str2Int(q) == 2 * Str2Int(old_q) + 1;
    } else {
      q := q + "0";
      assert Str2Int(q) == 2 * Str2Int(old_q);
      calc {
        Str2Int(dividend[..i + 1]);
      ==
        {assert dividend[..i + 1][..|dividend[..i + 1]| -1 ] == dividend[..i];}
        2 * Str2Int(dividend[..i]) + d;
      ==
        2 * (Str2Int(old_r) + Str2Int(old_q) * Str2Int(divisor)) + d;
      ==
        2 * Str2Int(old_q) * Str2Int(divisor) + (2 * Str2Int(old_r) + d);
      ==
        Str2Int(q) * Str2Int(divisor) + Str2Int(r);
      }
    }

  }
  calc {
    Str2Int(dividend);
  ==
    {assert dividend[..|dividend|] == dividend;}
    Str2Int(dividend[..|dividend|]);
  ==
    Str2Int(r) + Str2Int(q) * Str2Int(divisor);
  }
  assert Str2Int(r) < Str2Int(divisor);

  quotient := q;
  remainder := r;
  QuotientIsEquivalent(Str2Int(dividend), Str2Int(divisor), Str2Int(quotient), Str2Int(remainder));
}

lemma QuotientIsEquivalent(dividend : nat, divisor: nat, quotient: nat, remainder: nat)
  requires dividend == divisor * quotient + remainder
  ensures  dividend / divisor == quotient
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
