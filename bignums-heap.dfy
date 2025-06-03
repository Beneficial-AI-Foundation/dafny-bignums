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
  {
    firstTime := false;
    var ul := heap[up];
    up := up + 1;
    var vl := heap[vp];
    vp := vp + 1;
    var sl := ul + vl;
    var cy1 := if sl < ul then 1 else 0;
    var rl := sl + cy;
    var cy2 := if rl < sl then 1 else 0;
    cy := cy1 | cy2;
    heap[rp] := rl;
    rp := rp + 1;
    n := n-1;
  }

  return cy;
}

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
