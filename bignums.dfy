// Below is a self-contained Dafny program that:

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

// Theo note: To check that Add/Sub/Mul only use Int2Str and Str2Int for verification:
// 1. Change those functions to `ghost function`
// 2. Delete Main (because it uses those functions in executable code, so now won't verify)
// 3. The rest of the code will still verify

opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}


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

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}


opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}


lemma IgnoreInitialZeros(s : string, numZeros:int)
  requires ValidBitString(s)
  requires 0<=numZeros<=|s|
  requires forall i :: 0<=i<numZeros ==> s[i] == '0'
  ensures Str2Int(s) == Str2Int(s[numZeros..])
{
  if numZeros == 0 {
    return;
  }
  if numZeros == |s| {
    assert Str2Int(s) == (2 * Str2Int(s[0..|s|-1]));
    IgnoreInitialZeros(s[..|s|-1], numZeros-1);
    return;
  }
  IgnoreInitialZeros(s[..|s|-1], numZeros);
  var t := s[numZeros..];
  calc {
    Str2Int(s);
  ==
    (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  ==
    (2 * Str2Int(s[numZeros..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
  ==
    {
      assert t[..|t|-1] == s[numZeros..|s|-1];
      assert t[|t|-1] == s[|s|-1];
    }
    (2 * Str2Int(t[..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
  ==
    Str2Int(t);
  }
}


// Claude was able to mostly prove this one via calc.
// I wonder if it could be slightly easier to read by
// defining t := s[0..i+1] and expanding Str2Int(t)
lemma BitStringDecomposition(s: string, i: int)
  requires ValidBitString(s) && i < |s|
  ensures i >= 0 ==> Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{
  if i >= 0 {
    calc {
      Str2Int(s[0..i+1]);
    == // By definition of Str2Int
      if |s[0..i+1]| == 0 then 0
      else (2 * Str2Int(s[0..i+1][0..|s[0..i+1]|-1]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0));
    == // Since i >= 0, |s[0..i+1]| = i+1 > 0
      2 * Str2Int(s[0..i+1][0..|s[0..i+1]|-1]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    == // Simplify: s[0..i+1][0..|s[0..i+1]|-1] = s[0..i+1][0..i] = s[0..i]
      2 * Str2Int(s[0..i+1][0..i]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    ==
      { assert  s[0..i+1][0..i] == s[0..i];}
      2 * Str2Int(s[0..i]) + (if s[0..i+1][|s[0..i+1]|-1] == '1' then 1 else 0);
    ==
      2 * Str2Int(s[0..i]) + (if s[0..i+1][i] == '1' then 1 else 0);
    == // Simplify: s[0..i+1][i] = s[i]
      2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
    }
  }
}



lemma PrependDigitToString(digit: int, s: string)
  requires ValidBitString(s) && (digit == 0 || digit == 1)
  ensures Str2Int(if digit == 1 then ['1'] + s else ['0'] + s) ==
          Str2Int(s) + digit * Pow2(|s|)
{
  reveal Pow2();
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant Str2Int(if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]) == Str2Int(s[..i]) + digit * Pow2(|s[..i]|)
  {
    var t := if digit == 1 then ['1'] + s[..i+1] else ['0'] + s[..i+1];
    calc {
      Str2Int(t);
    ==
      if |t| == 0 then  0  else  (2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0));
    ==
      {assert |t| != 0;}
      2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    ==
      {
        assert t[|t|-1] == s[i];
        assert t[0..|t|-1] == (if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]);
      }
      2 * Str2Int(if digit == 1 then ['1'] + s[..i] else ['0'] + s[..i]) + (if s[i] == '1' then 1 else 0);
    ==
      2 * (Str2Int(s[..i]) + digit * Pow2(|s[..i]|)) + (if s[i] == '1' then 1 else 0);
    ==
      {
        var u := s[..i+1];
        calc {
          2 * Str2Int(s[..i]) + (if s[i] == '1' then 1 else 0);
        ==
          { assert s[..i] == u[0..|u|-1];
            assert s[i] == u[|u|-1];
          }
          2 * Str2Int(u[0..|u|-1]) + (if u[|u|-1] == '1' then 1 else 0);
        ==
          Str2Int(s[..i+1]);
        }
      }
      Str2Int(s[..i+1]) + digit * Pow2(|s[..i+1]|);
    }

    i:= i+1;
  }
  assert s[..i] == s;
}

lemma Bound(s : string)
  requires ValidBitString(s)
  ensures Pow2(|s|) > Str2Int(s)
{
  if |s| == 0 {
    Pow2Zero();
  }
  else {
    calc {
      Str2Int(s);
    ==
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    <=
      {Bound(s[0..|s|-1]);}
      2 * (Pow2(|s[0..|s|-1]|)-1) + (if s[|s|-1] == '1' then 1 else 0);
    ==
      2 * Pow2(|s|-1) - 2  + (if s[|s|-1] == '1' then 1 else 0);
    <=
      2 * Pow2(|s|-1) - 1;
    ==
      {Pow2Inductive(|s|-1);}
      Pow2(|s|) - 1;
    <
      Pow2(|s|);
    }
  }

}

lemma TrailingZeros(s: string, numZeros: nat)
  requires ValidBitString(s)
  requires numZeros <= |s|
  requires forall i :: |s| - numZeros <= i < |s| ==> s[i] == '0'
  ensures Str2Int(s) == Str2Int(s[..|s|-numZeros]) * Pow2(numZeros)
{
  if numZeros == 0 {
    calc {
      Str2Int(s[..|s|-numZeros]) * Pow2(numZeros);
    ==
      {Pow2Zero();}
      Str2Int(s[..|s|]) * 1;
    ==
      {assert s[..|s|] == s;}
      Str2Int(s);
    }
    return;
  }
  calc {
    Str2Int(s);
  ==
    2 * Str2Int(s[..|s|-1]);
  ==
    {TrailingZeros(s[..|s|-1], numZeros-1);
     assert s[..|s|-1][..|s|-numZeros] == s[..|s|-numZeros];
    }
    2 * (Str2Int(s[..|s|-numZeros]) * Pow2(numZeros-1));
  ==
    Str2Int(s[..|s|-numZeros]) * Pow2(numZeros-1) * 2;
  ==
    Str2Int(s[..|s|-numZeros]) * (Pow2(numZeros-1) * 2);
  ==
    {
      Pow2Inductive(numZeros-1);
    }
    Str2Int(s[..|s|-numZeros]) * Pow2(numZeros);
  }
}

// Useful because Dafny often struggles with this step
// in complicated expressions
lemma MulIsAssociative(a: nat, b: nat, c: nat)
  ensures a * (b * c) == a * b * c
{
}


lemma Expand(A:nat, B:nat, C:nat)
  ensures A * (B + 1) * C == A * C + A * B * C
{
}

lemma Rearrange(A:int, B:int, C:int)
  ensures (A * 2 + B) * C == A * 2 * C + B * C
{
}


// ----------------------------------------------------
// Int2Str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
function Int2Str(n: nat): string
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


lemma Eleven()
  ensures Str2Int("1011") == 11
{
  var s := "1011";
  calc {
    Str2Int(s);
  ==
    2*Str2Int(s[..3]) + 1;
  ==
    {assert s[..3] == "101";}
    2*Str2Int("101") + 1;
  ==
    {
      assert 2*Str2Int("10")+1 == Str2Int("101");}
    2*(2*Str2Int("10")+1) + 1;
  ==
    4*Str2Int("10") + 3;
  ==
    11;}
}

lemma Thirteen()
  ensures Str2Int("1101") == 13
{
  var s := "1101";
  calc {
    Str2Int(s);
  ==
    2*Str2Int(s[..3]) + 1;
  ==
    {assert s[..3] == "110";}
    2*Str2Int("110") + 1;
  ==
    {
      assert 2*Str2Int("11")+0 == Str2Int("110");}
    2*(2*Str2Int("11")+0) + 1;
  ==
    4*Str2Int("11") + 1;
  ==
    {assert Str2Int("11") == 3;}
    4*3 + 1;
  ==
    13;
  }
}


// I pulled this code out of `Add` in the hope that Dafny would avoid timeouts
// if it was in the narrower context of a lemma. Unfortunately that didn't
// fix the timeouts, but `Add` is easier to read with this long calculation removed.
// Annoyingly if you remove {:isolate_assertions}, this lemma sometimes times out.
// So really I need to go over it again to reduce brittleness, as in
// https://dafny.org/blog/2023/12/01/avoiding-verification-brittleness/
// I didn't check whether some of the intermediate steps can be taken out
lemma {:isolate_assertions} AddAux(x: string, y: string, oldSb: string, sb: string, oldI: int,
                                   oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= carry <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires sum == bitX + bitY + oldCarry
  requires digit == sum % 2
  requires carry == sum / 2
  requires (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          Str2Int(sb) +
          (carry * Pow2(|sb|)) +
          (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
          (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  calc {
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0);
  == // Split the x[0..oldI+1] into x[0..oldI] and the last bit
    {
      BitStringDecomposition(x, oldI);
      BitStringDecomposition(y, oldJ);
    }



    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0);

  == // Start distributing Pow2(|oldSb|) in the third term
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0);

  == // Use associative property: (a * b) * c = a * (b * c) in the third term
    {
      if oldI >= 0 {
        assert (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) == Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|));
      }
    }
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) + bitX * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0);

  == // Apply identity: 2 * Pow2(n) = Pow2(n+1) in the third term
    {
      assert Pow2(|oldSb| + 1) == 2 * Pow2(|oldSb|) by {
        Pow2Inductive(|oldSb|);
      }
    }
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0);

  == // Start distributing Pow2(|oldSb|) in the fourth term
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0);

  == // Use associative property in the fourth term
    {
      if oldJ >= 0 {
        assert (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) == Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|));
      }
    }
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) + bitY * Pow2(|oldSb|) else 0);

  == // Apply identity: 2 * Pow2(n) = Pow2(n+1) in the fourth term
    {
      Pow2Inductive(|oldSb|);
    }
    Str2Int(oldSb) +
    (oldCarry * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) + bitY * Pow2(|oldSb|) else 0);
  ==
    Str2Int(oldSb) +
    ((oldCarry * Pow2(|oldSb|)) +
     (if oldI >= 0 then bitX else 0) * Pow2(|oldSb|)) + (if oldJ >= 0 then bitY else 0) * Pow2(|oldSb|) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0);
  ==
    Str2Int(oldSb) +
    ((oldCarry * Pow2(|oldSb|)) + ((if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0)) * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0);
  == // Group bitX, bitY and oldCarry terms
    Str2Int(oldSb) +
    ((oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0)) * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0);
  == // By definition of sum in the code
    {
      assert oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0) == sum;
    }
    Str2Int(oldSb) +
    (sum * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0);
  == // sum = 2*carry + digit
    Str2Int(oldSb) +
    ((2 * carry + digit) * Pow2(|oldSb|)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0);
  == // Distribute Pow2(|oldSb|)
    {
      calc {
        ((2 * carry + digit) * Pow2(|oldSb|));
        2 * carry * Pow2(|oldSb|) + digit * Pow2(|oldSb|);
        {
          Pow2Inductive(|oldSb|);
        }
        (digit * Pow2(|oldSb|)) + (carry * Pow2(|oldSb| + 1));
      }
    }
    Str2Int(oldSb) +
    (digit * Pow2(|oldSb|)) +
    (carry * Pow2(|oldSb| + 1)) +
    (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0);
  == // Definition of Str2Int for new digit + oldSb
    {
      PrependDigitToString(digit, oldSb);
    }
    Str2Int(if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) +
    (carry * Pow2(|oldSb| + 1)) +
    (if oldI - 1 >= 0 then Str2Int(x[0..(oldI-1)+1]) * Pow2(|oldSb| + 1) else 0) +
    (if oldJ - 1 >= 0 then Str2Int(y[0..(oldJ-1)+1]) * Pow2(|oldSb| + 1) else 0);
  == // By definition of sb and updated i, j
    {
      assert Pow2(|sb|) == Pow2(|oldSb| + 1);
      assert (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb;
    }
    Str2Int(sb) +
    (carry * Pow2(|sb|)) +
    (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
    (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0);
  }
}

// Lemma 1: Apply BitStringDecomposition for both numbers
lemma SubAux1(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then (OStr2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then (OStr2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  reveal OStr2Int;
  BitStringDecomposition(x, oldI);
  BitStringDecomposition(y, oldJ);
}

// Lemma 2: Distribute Pow2(|oldSb|)
lemma SubAux2(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then (OStr2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then (OStr2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * 2 * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * 2 * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    assert (OStr2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) == OStr2Int(x[0..oldI]) * 2 * Pow2(|oldSb|) + bitX * Pow2(|oldSb|);
  }
  if oldJ >= 0 {
    var A := OStr2Int(y[0..oldJ]);
    var B := bitY;
    var C := Pow2(|oldSb|);
    Rearrange(A, B, C);
  }
}

// Lemma 3: Use Pow2 relationship: 2 * Pow2(n) = Pow2(n+1)
lemma SubAux3(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * 2 * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * 2 * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) + bitY * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    var A := OStr2Int(x[0..oldI]);
    var B := Pow2(|oldSb|);
    assert (A * 2) * B == A * (2 * B) by { MulIsAssociative(A, 2, B); }
    Pow2Inductive(|oldSb|);
    assert Pow2(|oldSb|+1) == 2 * Pow2(|oldSb|);
  }

  if oldJ >= 0 {
    var A := OStr2Int(y[0..oldJ]);
    var B := Pow2(|oldSb|);
    assert (A * 2) * B == A * (2 * B) by { MulIsAssociative(A, 2, B); }
    Pow2Inductive(|oldSb|);
    assert Pow2(|oldSb|+1) == 2 * Pow2(|oldSb|);
  }
}

// Lemma 4: Rearrange to isolate the digit contribution
lemma SubAux4(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) + bitX * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) + bitY * Pow2(|oldSb|) else 0) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) * Pow2(|oldSb|)
{
  // Rearrangement step - just algebraic manipulation
}

// Lemma 5: By the definition of diff in code
lemma SubAux5(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) * Pow2(|oldSb|) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (rawDiff * Pow2(|oldSb|))
{
  assert ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff;
}

// Lemma 6: Apply relationship between rawDiff, diff and borrow
lemma SubAux6(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (rawDiff * Pow2(|oldSb|)) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if rawDiff < 0 then diff - 2 else diff) * Pow2(|oldSb|))
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

// Lemma 7: Rewrite in terms of borrow
lemma SubAux7(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          ((if rawDiff < 0 then diff - 2 else diff) * Pow2(|oldSb|)) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (if borrow == 1 then 2 * Pow2(|oldSb|) else 0))
{
  // Rewrite using borrow
}

// Lemma 8: Use Pow2 relationship again
lemma SubAux8(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (if borrow == 1 then 2 * Pow2(|oldSb|) else 0)) ==
          OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (borrow * Pow2(|oldSb|+1)))
{
  if borrow == 1 {
    assert 2 * Pow2(|oldSb|) == Pow2(|oldSb|+1) by { Pow2Inductive(|oldSb|); }
  }
}

// Lemma 9: Rearrange terms
lemma SubAux9(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) +
          (if oldI >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) +
          (diff * Pow2(|oldSb|) - (borrow * Pow2(|oldSb|+1))) ==
          OStr2Int(oldSb) +
          diff * Pow2(|oldSb|) +
          (if i >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if j >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) -
          (borrow * Pow2(|oldSb|+1))
{
  reveal OStr2Int;
}

// Lemma 10: Apply PrependDigitToString
lemma SubAux10(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) +
          diff * Pow2(|oldSb|) +
          (if i >= 0 then OStr2Int(x[0..oldI]) * Pow2(|oldSb|+1) else 0) -
          (if j >= 0 then OStr2Int(y[0..oldJ]) * Pow2(|oldSb|+1) else 0) -
          (borrow * Pow2(|oldSb|+1)) ==
          OStr2Int(if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) +
          (if i >= 0 then OStr2Int(x[0..i+1]) * Pow2(|oldSb|+1) else 0) -
          (if j >= 0 then OStr2Int(y[0..j+1]) * Pow2(|oldSb|+1) else 0) -
          (borrow * Pow2(|oldSb|+1))
{
  // Apply PrependDigitToString to convert the expression
  reveal OStr2Int;
  PrependDigitToString(diff, oldSb);

  // Establish that sb == (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb)
  assert sb == (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb);

  // Establish relationships between indices when working with slices
  if i >= 0 {
    assert oldI >= 0 && i == oldI - 1;
    assert x[0..i+1] == x[0..oldI];  // Since i+1 == oldI
  }

  if j >= 0 {
    assert oldJ >= 0 && j == oldJ - 1;
    assert y[0..j+1] == y[0..oldJ];  // Since j+1 == oldJ
  }
}



// Top-level lemma that combines all the individual steps
lemma SubAuxTop(x: string, y: string, oldSb: string, sb: string, oldI: int,
                oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires ValidBitString(sb)
  requires ValidBitString(x)
  requires ValidBitString(y)
  requires ValidBitString(oldSb)
  requires 0 <= borrow <= 1
  requires i <= |x| - 1 && j <= |y| - 1
  requires oldI <= |x| - 1 && oldJ <= |y| - 1
  requires i >= -1
  requires j >= -1
  requires oldI >= 0 ==> i == oldI - 1
  requires oldJ >= 0 ==> j == oldJ - 1
  requires oldI < 0 ==> i == oldI
  requires oldJ < 0 ==> j == oldJ
  requires oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)
  requires oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)
  requires oldI < 0 ==> bitX == 0
  requires oldJ < 0 ==> bitY == 0
  requires |oldSb| == |sb| - 1
  requires (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
  requires ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff
  requires rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1
  requires rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0
  ensures OStr2Int(oldSb) -
          (oldBorrow * Pow2(|oldSb|)) +
          (if oldI >= 0 then OStr2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) -
          (if oldJ >= 0 then OStr2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          OStr2Int(sb) -
          (borrow * Pow2(|sb|)) +
          (if i >= 0 then OStr2Int(x[0..i+1]) * Pow2(|sb|) else 0) -
          (if j >= 0 then OStr2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  // Call all the sub-lemmas in sequence to establish the proof
  SubAux1(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux2(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux3(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux4(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux5(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux6(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux7(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux8(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux9(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);
  SubAux10(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow);

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

    AddAux(x, y, oldSb, sb, oldI,
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
  var sb := [];  // reversed result

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
method {:isolate_assertions} Mul(s1: string, s2: string) returns (res: string)
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
    }
    shift := shift + ['0'];
    idx := idx - 1;
    assert ValidBitString(y[..idx+1] + shift);
    if y[idx+1] == '0' {
      calc {
        OStr2Int(x) * OStr2Int(y);
      ==
        OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift);
      ==
        {
          assert prevProduct == product;
          assert y[..idx+2] + prevShift == y[..idx+1] + shift;
        }
        OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
      }
    }
    else {
      var a := |shift|;
      calc {
        OStr2Int(x) * OStr2Int(y);
      ==
        OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift);
      ==
        { assert y[..idx+2] + prevShift == y[..idx+1] + "1" + prevShift;}
        OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift);
      ==
        { TrailingZeros(y[..idx+1] + "1" + prevShift, a-1);
          assert OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(y[..idx+1] + "1") * Pow2(a-1) by {reveal OStr2Int;}
          assert OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(x) * (OStr2Int(y[..idx+1] + "1") * Pow2(a-1));
          assert OStr2Int(x) * (OStr2Int(y[..idx+1] + "1") * Pow2(a-1)) == OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1)
          by {MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1] + "1"), Pow2(a-1));}

          assert OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1);
        }
        OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1);
      ==
        {reveal OStr2Int;
        }
        OStr2Int(prevProduct) + OStr2Int(x) * (2*OStr2Int(y[..idx+1]) + 1) * Pow2(a-1);
      ==
        {
          Expand(OStr2Int(x), 2*OStr2Int(y[..idx+1]), Pow2(a-1));
        }
        OStr2Int(prevProduct) + OStr2Int(x) * Pow2(a-1) + OStr2Int(x) * (2*OStr2Int(y[..idx+1])) * Pow2(a-1);
      ==
        {assert OStr2Int(x) * Pow2(a-1) == OStr2Int(x + prevShift) by {

           reveal OStr2Int;
           TrailingZeros(x+ prevShift, a-1);
         }
         calc {
           OStr2Int(x) * (2*OStr2Int(y[..idx+1])) * Pow2(a-1);
         ==
           {
             MulIsAssociative(OStr2Int(x), 2*OStr2Int(y[..idx+1]), Pow2(a-1));
           }
           OStr2Int(x) * ((2*OStr2Int(y[..idx+1])) * Pow2(a-1));
         ==
           {
             assert (2*OStr2Int(y[..idx+1])) * Pow2(a-1) == OStr2Int(y[..idx+1]) * Pow2(a)
             by{
               Pow2Inductive(a-1);
             }
           }
           OStr2Int(x) * (OStr2Int(y[..idx+1]) * Pow2(a));
         ==
           {MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1]), Pow2(a));}
           OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a);
         }
        }
        OStr2Int(prevProduct) + OStr2Int(x + prevShift) + OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a);
      ==
        {
          assert OStr2Int(y[..idx+1]) * Pow2(a) ==  OStr2Int(y[..idx+1] + shift) by {
            reveal OStr2Int;
            TrailingZeros(y[..idx+1] + shift, a);
          }
          MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1]), Pow2(a));
          assert OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a) ==  OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
        }
        OStr2Int(prevProduct) + OStr2Int(x + prevShift) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
      ==
        {reveal OStr2Int;}
        OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
      }
    }
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
