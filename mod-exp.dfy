
// This function will be useful in proofs
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// This function will be useful in proofs
opaque function Exp(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Pow2(y - 1)
}



// Establish some properties of Pow2

lemma Pow2Zero()
  ensures Pow2(0) == 1
{
  reveal Pow2();
}

lemma Pow2Inductive(i: nat)
  ensures Pow2(i+1) == 2*Pow2(i)
{
  reveal Pow2();
}


predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}


method ModExp(x: string, y: string, z: string) returns (res: string)
    requires ValidBitString(x) && ValidBitString(y) &&  ValidBitString(z)
    ensures ValidBitString(res)
    ensures Str2Int(res) == Exp(Str2Int(x), Str2Int(y)) % Str2Int(z) 
{

}

function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}



