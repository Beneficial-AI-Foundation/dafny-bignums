
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

// The proof of Add's invariant requires a long calculation that often times
// out. To make it more robust, I've pulled it into a lemma AddAuxTop, which
// then calls 14 lemmas, one for each step of the calculation. For conciseness,
// all the lemmas use AddAuxPred as their precondition (although not all of them
// need all of AddAuxPred)

predicate AddAuxPred(x: string, y: string, oldSb: string, sb: string, oldI: int,
                     oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
{
  ValidBitString(sb) &&
  ValidBitString(x) &&
  ValidBitString(y) &&
  ValidBitString(oldSb) &&
  0 <= carry <= 1 &&
  i <= |x| - 1 && j <= |y| - 1 &&
  oldI <= |x| - 1 && oldJ <= |y| - 1 &&
  i >= -1 &&
  j >= -1 &&
  (oldI >= 0 ==> i == oldI - 1) &&
  (oldJ >= 0 ==> j == oldJ - 1) &&
  (oldI < 0 ==> i == oldI) &&
  (oldJ < 0 ==> j == oldJ) &&
  (oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)) &&
  (oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)) &&
  (oldI < 0 ==> bitX == 0) &&
  (oldJ < 0 ==> bitY == 0) &&
  |oldSb| == |sb| - 1 &&
  sum == bitX + bitY + oldCarry &&
  digit == sum % 2 &&
  carry == sum / 2 &&
  (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
}

// Lemma 1: Apply BitStringDecomposition for both numbers
lemma AddAux1(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  BitStringDecomposition(x, oldI);
  BitStringDecomposition(y, oldJ);
}

// Lemma 2: Distribute Pow2(|oldSb|) in the third term
lemma AddAux2(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2 + bitX) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    var A := Str2Int(x[0..oldI]);
    var B := bitX;
    var C := Pow2(|oldSb|);
    Rearrange(A, B, C);
  }
}


// Lemma 3: Use associative property in the third term
lemma AddAux3(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  if oldI >= 0 {
    assert (Str2Int(x[0..oldI]) * 2) * Pow2(|oldSb|) == Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) by {
      MulIsAssociative(Str2Int(x[0..oldI]), 2, Pow2(|oldSb|));
    }
  }
}

// Lemma 4: Apply identity: 2 * Pow2(n) = Pow2(n+1) in the third term
lemma AddAux4(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * (2 * Pow2(|oldSb|)) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0)
{
  assert Pow2(|oldSb| + 1) == 2 * Pow2(|oldSb|) by {
    Pow2Inductive(|oldSb|);
  }
}

// Lemma 5: Start distributing Pow2(|oldSb|) in the fourth term
lemma AddAux5(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2 + bitY) * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0)
{
  if oldJ >= 0 {
    var A := Str2Int(y[0..oldJ]);
    var B := bitY;
    var C := Pow2(|oldSb|);
    Rearrange(A, B, C);
  }
}

// Lemma 6: Use associative property in the fourth term
lemma AddAux6(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) + bitY * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) + bitY * Pow2(|oldSb|) else 0)
{
  if oldJ >= 0 {
    assert (Str2Int(y[0..oldJ]) * 2) * Pow2(|oldSb|) == Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) by {
      MulIsAssociative(Str2Int(y[0..oldJ]), 2, Pow2(|oldSb|));
    }
  }
}

// Lemma 7: Apply identity: 2 * Pow2(n) = Pow2(n+1) in the fourth term
lemma AddAux7(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * (2 * Pow2(|oldSb|)) + bitY * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) + bitY * Pow2(|oldSb|) else 0)
{
  Pow2Inductive(|oldSb|);
}

// Lemma 8: Rearrange terms
lemma AddAux8(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) + bitX * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) + bitY * Pow2(|oldSb|) else 0) ==
          Str2Int(oldSb) +
          ((oldCarry * Pow2(|oldSb|)) +
           (if oldI >= 0 then bitX else 0) * Pow2(|oldSb|)) + (if oldJ >= 0 then bitY else 0) * Pow2(|oldSb|) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  // Simple rearrangement of terms
}

// Lemma 9: Group bit terms
lemma AddAux9(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          ((oldCarry * Pow2(|oldSb|)) +
           (if oldI >= 0 then bitX else 0) * Pow2(|oldSb|)) + (if oldJ >= 0 then bitY else 0) * Pow2(|oldSb|) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          ((oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0)) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  // Grouping terms with the same factor Pow2(|oldSb|)
}

// Lemma 10: By definition of sum in the code
lemma AddAux10(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          ((oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0)) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          (sum * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  assert oldCarry + (if oldI >= 0 then bitX else 0) + (if oldJ >= 0 then bitY else 0) == sum;
}

// Lemma 11: sum = 2*carry + digit
lemma AddAux11(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (sum * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          ((2 * carry + digit) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  assert sum == 2 * carry + digit by {
    assert carry == sum / 2;
    assert digit == sum % 2;
    assert sum == (sum / 2) * 2 + (sum % 2);
  }
}

// Lemma 12: Distribute Pow2(|oldSb|)
lemma AddAux12(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          ((2 * carry + digit) * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(oldSb) +
          (digit * Pow2(|oldSb|)) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0)
{
  calc {
    ((2 * carry + digit) * Pow2(|oldSb|));
  ==
    2 * carry * Pow2(|oldSb|) + digit * Pow2(|oldSb|);
  ==
    {
      Pow2Inductive(|oldSb|);
    }
    (digit * Pow2(|oldSb|)) + (carry * Pow2(|oldSb| + 1));
  }
}

// Lemma 13: Definition of Str2Int for new digit + oldSb
lemma AddAux13(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (digit * Pow2(|oldSb|)) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI >= 0 then Str2Int(x[0..oldI]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI - 1 >= 0 then Str2Int(x[0..(oldI-1)+1]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ - 1 >= 0 then Str2Int(y[0..(oldJ-1)+1]) * Pow2(|oldSb| + 1) else 0)
{
  PrependDigitToString(digit, oldSb);
}

// Lemma 14: By definition of sb and updated i, j
lemma AddAux14(x: string, y: string, oldSb: string, sb: string, oldI: int,
               oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) +
          (carry * Pow2(|oldSb| + 1)) +
          (if oldI - 1 >= 0 then Str2Int(x[0..(oldI-1)+1]) * Pow2(|oldSb| + 1) else 0) +
          (if oldJ - 1 >= 0 then Str2Int(y[0..(oldJ-1)+1]) * Pow2(|oldSb| + 1) else 0) ==
          Str2Int(sb) +
          (carry * Pow2(|sb|)) +
          (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
          (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  assert Pow2(|sb|) == Pow2(|oldSb| + 1);
  assert (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb;

  if oldI >= 0 {
    assert i == oldI - 1;
    if i >= 0 {
      assert x[0..i+1] == x[0..oldI];
    }
  }

  if oldJ >= 0 {
    assert j == oldJ - 1;
    if j >= 0 {
      assert y[0..j+1] == y[0..oldJ];
    }
  }
}

// Top-level lemma that combines all the individual steps
lemma AddAuxTop(x: string, y: string, oldSb: string, sb: string, oldI: int,
                oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          Str2Int(sb) +
          (carry * Pow2(|sb|)) +
          (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
          (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
  // Call all the sub-lemmas in sequence to establish the proof
  AddAux1(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux2(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux3(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux4(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux5(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux6(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux7(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux8(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux9(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux10(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux11(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux12(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux13(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
  AddAux14(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
}

// Sub also has a long calcuation step, which again we split into a bunch of lemmas

predicate SubAuxPred(x: string, y: string, oldSb: string, sb: string, oldI: int,
                     oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
{
  ValidBitString(sb) &&
  ValidBitString(x) &&
  ValidBitString(y) &&
  ValidBitString(oldSb) &&
  0 <= borrow <= 1 &&
  i <= |x| - 1 && j <= |y| - 1 &&
  oldI <= |x| - 1 && oldJ <= |y| - 1 &&
  i >= -1 &&
  j >= -1 &&
  (oldI >= 0 ==> i == oldI - 1) &&
  (oldJ >= 0 ==> j == oldJ - 1) &&
  (oldI < 0 ==> i == oldI) &&
  (oldJ < 0 ==> j == oldJ) &&
  (oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)) &&
  (oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)) &&
  (oldI < 0 ==> bitX == 0) &&
  (oldJ < 0 ==> bitY == 0) &&
  |oldSb| == |sb| - 1 &&
  (if diff == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb &&
  ((if oldI >= 0 then bitX else 0) - (if oldJ >= 0 then bitY else 0) - oldBorrow) == rawDiff &&
  (rawDiff < 0 ==> (diff == rawDiff + 2) && borrow == 1) &&
  (rawDiff >= 0 ==> (diff == rawDiff) && borrow == 0)
}

// Lemma 1: Apply BitStringDecomposition for both numbers
lemma SubAux1(x: string, y: string, oldSb: string, sb: string, oldI: int,
              oldJ: int, i:int, j:int, borrow:nat, bitX:nat, bitY:nat, rawDiff:int, diff:nat, oldBorrow:nat)
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
  requires SubAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, borrow, bitX, bitY, rawDiff, diff, oldBorrow)
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
