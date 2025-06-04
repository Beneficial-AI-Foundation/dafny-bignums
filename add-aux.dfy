
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
