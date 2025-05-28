include "bignums.dfy"


// computes res := x^y when y == 2^n
opaque function Exp(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Pow2(y - 1)
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
