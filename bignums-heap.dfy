include "pow2.dfy"

// Based on line 37 of https://github.com/gmp-mirror/gmp/blob/master/mpn/generic/add_n.c
// The pointers point to arrays of bits, but for an
// efficient version it should be something like array<bv64>
method MpnAddN(heap: array<bv1>, rpConst: nat, upConst: nat, vpConst: nat, nConst: nat) returns (cy: bv1)
  modifies heap
  requires upConst + nConst < heap.Length
  requires vpConst + nConst < heap.Length
  requires rpConst + nConst < heap.Length
  requires nConst >= 1
  // Note that the pointers are allowed to overlap as long as
  // it's "in a way suitable for an incrementing/decrementing algorithm";
  // see gmp/gmp-impl.h, line 2467
  requires MpnSameOrIncrP(rpConst, upConst, nConst)
  requires MpnSameOrIncrP(rpConst, vpConst, nConst)
  ensures Pow2(nConst) * cy as nat + BitsToInt(heap[rpConst..rpConst+nConst]) ==
          BitsToInt(old(heap[upConst..upConst+nConst]))
          + BitsToInt(old(heap[vpConst..vpConst+nConst]))
  // This function does not modify any memory except the result:
  ensures heap[..rpConst] == old(heap[..rpConst])
  ensures heap[rpConst+nConst..] == old(heap[rpConst+nConst..])
{
  cy := 0;
  // Create mutable versions of these variables
  var rp := rpConst;
  var up := upConst;
  var vp := vpConst;
  var n := nConst;
  // The C code uses a do-while loop, so this while loop must execute at least once
  var firstTime := true;
  while firstTime || n != 0
    decreases n
    invariant 0 <= up <= up + n < heap.Length
    invariant 0 <= vp <= vp + n < heap.Length
    invariant 0 <= rp <= rp + n < heap.Length
    invariant !firstTime || n >= 1
    invariant heap[rpConst+nConst..] == old(heap[rpConst+nConst..])
    invariant heap[..rpConst] == old(heap[..rpConst])
    invariant rp + n == rpConst + nConst
    invariant up + n == upConst+nConst
    invariant vp + n == vpConst+nConst
    invariant upConst <= up
    invariant vpConst <= vp
    invariant Pow2(rp - rpConst) * cy as nat + BitsToInt(heap[rpConst..rp]) ==
              BitsToInt(old(heap[upConst..up])) + BitsToInt(old(heap[vpConst..vp]))
    invariant heap[up..upConst+nConst] == old(heap[up..upConst+nConst])
    invariant heap[vp..vpConst+nConst] == old(heap[vp..vpConst+nConst])
  {
    ghost var old_rp := rp;
    ghost var old_cy := cy;
    ghost var old_up := up;
    ghost var old_vp := vp;
    firstTime := false;

    reveal MpnSameOrIncrP();
    reveal MpnSameOrIncrP2();
    reveal MpnOverlapP();
    
    // Establish that up hasn't been modified in a way that would invalidate array contents
    assert MpnSameOrIncrP(rpConst, upConst, nConst);
    assert MpnSameOrIncrP2(rpConst, nConst, upConst, nConst);
    assert (rpConst <= upConst) || !MpnOverlapP(rpConst, nConst, upConst, nConst);
    
    var ul := heap[up];
    assert ul == old(heap[old_up]);
    up := up + 1;
    var vl := heap[vp];
    assert vl == old(heap[old_vp]);
    vp := vp + 1;
    var sl := ul + vl;
    var cy1 := if sl < ul then 1 else 0;
    var rl := sl + cy;
    var cy2 := if rl < sl then 1 else 0;
    cy := cy1 | cy2;
    heap[rp] := rl;
    rp := rp + 1;
    n := n-1;
    calc {
      Pow2(rp - rpConst) * cy as nat + BitsToInt(heap[rpConst..rp]);
    == // Substitute rp = old_rp + 1
      Pow2(old_rp + 1 - rpConst) * cy as nat + BitsToInt(heap[rpConst..old_rp+1]);
    == // Simplify exponent
      Pow2(old_rp - rpConst + 1) * cy as nat + BitsToInt(heap[rpConst..old_rp+1]);
    == // Using Pow2(n+1) = 2 * Pow2(n)
      {reveal Pow2;}
      2 * Pow2(old_rp - rpConst) * cy as nat + BitsToInt(heap[rpConst..old_rp+1]);
    == // Using BitsToIntAppend lemma
      {BitsToIntAppend(heap[rpConst..old_rp], heap[old_rp]);
       assert heap[rpConst..old_rp+1] == heap[rpConst..old_rp] + [heap[old_rp]];}
      2 * Pow2(old_rp - rpConst) * cy as nat + BitsToInt(heap[rpConst..old_rp]) + rl as nat * Pow2(old_rp - rpConst);
    == // Factor out Pow2(old_rp - rpConst)
      Pow2(old_rp - rpConst) * (2 * cy as nat + rl as nat) + BitsToInt(heap[rpConst..old_rp]);
    == // Based on binary addition with carry
      Pow2(old_rp - rpConst) * (ul as nat + vl as nat + old_cy as nat) + BitsToInt(heap[rpConst..old_rp]);
    == // Using pre-state invariant
      Pow2(old_rp - rpConst) * (ul as nat + vl as nat) +
      (Pow2(old_rp - rpConst) * old_cy as nat + BitsToInt(heap[rpConst..old_rp]));
    == // Pre-state invariant value
      Pow2(old_rp - rpConst) * (ul as nat + vl as nat) +
      BitsToInt(old(heap[upConst..old_up])) + BitsToInt(old(heap[vpConst..old_vp]));
    == // Expand using old_up = up-1, old_vp = vp-1
      BitsToInt(old(heap[upConst..old_up])) + BitsToInt(old(heap[vpConst..old_vp])) +
      (ul as nat * Pow2(old_rp - rpConst) + vl as nat * Pow2(old_rp - rpConst));
    == // Applying BitsToIntAppend property
      {
        assert ul as nat * Pow2(old_rp - rpConst) == BitsToInt(old(heap[old_up..up]))  * Pow2(old_up - upConst);
        assert vl as nat * Pow2(old_rp - rpConst) == BitsToInt(old(heap[old_vp..vp]))  * Pow2(old_vp - vpConst);
      }
      BitsToInt(old(heap[upConst..old_up])) + BitsToInt(old(heap[vpConst..old_vp])) +
      BitsToInt(old(heap[old_up..up])) * Pow2(old_up - upConst) +
      BitsToInt(old(heap[old_vp..vp])) * Pow2(old_vp - vpConst);
    == // Simplification based on indices
      {
        BitsToIntAppend(old(heap[upConst..old_up]), old(heap[old_up]));
        BitsToIntAppend(old(heap[vpConst..old_vp]), old(heap[old_vp]));
        assert old(heap[upConst..up]) == old(heap[upConst..old_up+1]) == old(heap[upConst..old_up]) + [old(heap[old_up])];
        assert old(heap[vpConst..vp]) == old(heap[vpConst..old_vp+1]) == old(heap[vpConst..old_vp]) + [old(heap[old_vp])];
        assert BitsToInt(old(heap[upConst..up])) == BitsToInt(old(heap[upConst..old_up])) + BitsToInt(old(heap[old_up..up])) * Pow2(old_up - upConst);
        assert BitsToInt(old(heap[vpConst..vp])) == BitsToInt(old(heap[vpConst..old_vp])) + BitsToInt(old(heap[old_vp..vp])) * Pow2(old_vp - vpConst);
      }
      BitsToInt(old(heap[upConst..up])) + BitsToInt(old(heap[vpConst..vp]));
    }
  }


  return cy;
}

lemma BitsToIntAppend(bits: seq<bv1>, new_bit: bv1)
  ensures BitsToInt(bits + [new_bit]) == BitsToInt(bits) + (new_bit as int) * Pow2(|bits|)
{}


// These 3 predicates are from gmp/gmp-impl.h
opaque predicate MpnSameOrIncrP(dst: nat, src: nat, size: nat){
  MpnSameOrIncrP2(dst, size, src, size)
}

opaque predicate MpnSameOrIncrP2(dst: nat, dsize: nat, src: nat, ssize: nat) {
  (dst <= src) || !MpnOverlapP(dst, dsize, src, ssize)
}

opaque predicate MpnOverlapP(xp: nat, xsize: nat, yp: nat, ysize: nat) {
  (xp + xsize > yp) && (yp + ysize > xp)
}

// The C code is little-endian
ghost function BitsToInt(s: seq<bv1>): nat
{
  if |s| == 0 then  0  else  (2 * BitsToInt(s[1..]) + s[0] as int)
}

method Main() {

  var heap := new bv1[] [1, 0, 1, 1, // 13, little-endian
  1, 1, 0, 1, // 11
  0, 0, 0, 0];// empty memory to be filled in
  var up := 0;
  var vp := 4;
  var rp := 8;

  var cy := MpnAddN(heap, rp, up, vp, 4);

  print "These should still be 0, 4, 8\n";
  print "up ", up, "\n";
  print "vp ", vp, "\n";
  print "rp ", rp, "\n";

  print "heap ", heap[..], "\n";
  print "carry ", cy, "\n";

  print "16 * carry, plus the last 4 values from the heap (read in little-endian order), should be 24";
}
