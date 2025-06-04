
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
