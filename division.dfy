include "bignums.dfy"

method {:isolate_assertions} DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  // Handle special cases
  if dividend == "0" {
    quotient := "0";
    remainder := "0";
    return;
  }

  if Compare(dividend, divisor) < 0 {
    quotient := "0";
    remainder := dividend;
    calc {
      Str2Int(quotient);
    ==
      0;
    ==
      {
        assert Str2Int(divisor) > 0;
        assert Str2Int(divisor) > Str2Int(dividend);
      }
      Str2Int(dividend) / Str2Int(divisor);
      // TODO This doesn't verify, but do we need this special case?
    }
    return;
  }

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
    r := r + [dividend[i]];


    // Check if divisor can be subtracted from current remainder
    if Compare(r, divisor) >= 0 {
      // Subtract divisor from remainder
      r := Sub(r, divisor);
      q := q + "1";
    } else {
      q := q + "0";
    }

  }

  quotient := q;
  remainder := r;
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
