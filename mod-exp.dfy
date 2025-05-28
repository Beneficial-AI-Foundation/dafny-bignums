
// This function will be useful in proofs
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// computes res := x^y when y == 2^n
opaque function Exp(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Pow2(y - 1)
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  res := ""; // TO BE PLUGGED IN FROM OTHER FILES
  assume Str2Int(res) == Str2Int(s1) + Str2Int(s2);
  assume ValidBitString(res);
}

// computes res := x^y % z when y == 2^n
method ExpPow2(x: nat, y:nat, z: nat, n:nat) returns (res:nat)
  requires y == Pow2(n)
  ensures res == Exp(x,y) % z
{

}

// computes (s1^s2) % s3 for bignums s1,s2,s3 when s2 == 2^n
method ModExpPow2(s1: string, s2: string, s3: string, n: nat) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) &&  ValidBitString(s3)
  requires Str2Int(s2) == Pow2(n)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp(Str2Int(s1), Str2Int(s2)) % Str2Int(s3)
{

}


// computes (s1^s2) % s3 for bignums s1,s2,s3
method ModExp(s1: string, s2: string, s3: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2) &&  ValidBitString(s3)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp(Str2Int(s1), Str2Int(s2)) % Str2Int(s3)
{

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



