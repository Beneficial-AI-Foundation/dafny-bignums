include "pow2.dfy"
include "bitstrings.dfy"
// Establish some properties of Pow2
lemma Pow2Zero()
  ensures Pow2(0) == 1
{
  reveal Pow2();
}

lemma Pow2Positive(n:nat)
  ensures Pow2(n) > 0
{
  if n == 0 {
    Pow2Zero();
  }
  else {
    Pow2Positive(n-1);
    reveal Pow2();
  }
}

lemma Pow2Inductive(i: nat)
  ensures Pow2(i+1) == 2*Pow2(i)
{
  reveal Pow2();
}

// The next few lemmas will be needed
// at various steps in the main proofs

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

lemma Pow2Monotonic(a: nat, b:nat)
  requires a <= b
  ensures Pow2(a) <= Pow2(b)
{
  if b-a == 0 {
    return;
  }
  if b-a == 1 {
    reveal Pow2;
    return;
  }
  reveal Pow2;
  Pow2Monotonic(a, b-1);
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
      OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros);
    ==
      {Pow2Zero();}
      OStr2Int(s[..|s|]) * 1;
    ==
      {assert s[..|s|] == s;}
      OStr2Int(s);
    }
    reveal OStr2Int;
    return;
  }
  calc {
    OStr2Int(s);
  ==
    {reveal OStr2Int;}
    2 * OStr2Int(s[..|s|-1]);
  ==
    {TrailingZeros(s[..|s|-1], numZeros-1);
     assert s[..|s|-1][..|s|-numZeros] == s[..|s|-numZeros];
     reveal OStr2Int;
    }
    2 * (OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros-1));
  ==
    OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros-1) * 2;
  ==
    OStr2Int(s[..|s|-numZeros]) * (Pow2(numZeros-1) * 2);
  ==
    {
      Pow2Inductive(numZeros-1);
    }
    OStr2Int(s[..|s|-numZeros]) * Pow2(numZeros);
  }
  reveal OStr2Int;
}

// The next few lemmas are trivial, but they're useful when Dafny struggles with
// algebra in complicated expressions

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


// Eleven and Thirteen will be used in Main

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


// Helper lemma for maintaining the loop invariant in Mul
lemma MulAux(x: string, y: string, prevProduct: string, product: string,
             prevShift: string, shift: string, idx: int)
  requires ValidBitString(x) && ValidBitString(y)
  requires ValidBitString(prevProduct) && ValidBitString(product)
  requires ValidBitString(prevShift) && ValidBitString(shift)
  requires -1 <= idx < |y| - 1
  requires forall i :: 0 <= i < |prevShift| ==> prevShift[i] == '0'
  requires forall i :: 0 <= i < |shift| ==> shift[i] == '0'
  requires shift == prevShift + ['0']
  requires idx + 1 < |y|
  requires y[idx+1] == '0' ==> prevProduct == product
  requires y[idx+1] == '1' ==> OStr2Int(product) == OStr2Int(prevProduct)+ OStr2Int(x + prevShift)
  requires OStr2Int(x) * OStr2Int(y) == OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift)
  ensures OStr2Int(x) * OStr2Int(y) ==
          OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift) ==>
            OStr2Int(x) * OStr2Int(y) ==
            OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift)
{
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
