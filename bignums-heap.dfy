include "pow2.dfy"

// Based on line 37 of https://github.com/gmp-mirror/gmp/blob/master/mpn/generic/add_n.c
// The pointers point to arrays of bits, but for an
// efficient version it should be something like array<bv64>
method mpn_add_n(heap: array<bv1>, rp_const: nat, up_const: nat, vp_const: nat, n_const: nat) returns (cy: bv1)
  modifies heap
  requires n_const >= 1
  requires MpnSameOrIncrP(rp_const, up_const, n_const)
  requires MpnSameOrIncrP(rp_const, vp_const, n_const)
  // TODO require that rp, rp + n, up, up + n, vp, vp + n are in-bounds for the heap
  // TODO ensure that the only part of the heap that could change is heap[rp..rp+n]
  // Note that the pointers are allowed to overlap as long as
  // it's "in a way suitable for an incrementing/decrementing algorithm";
  // see gmp/gmp-impl.h, line 2467
  ensures Pow2(n_const) * cy as nat + BitsToInt(heap[rp_const..rp_const+n_const]) ==
          BitsToInt(old(heap[up_const..up_const+n_const]))
          + BitsToInt(old(heap[vp_const..vp_const+n_const]))
{
  cy := 0;
  // Create mutable versions of these variables
  var rp := rp_const;
  var up := up_const;
  var vp := vp_const;
  var n := n_const;
  // The C code uses a do-while loop, so this while loop must execute at least once
  var first_time := true;
  while first_time || n != 0
  {
    first_time := false;
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
opaque predicate MpnSameOrIncrP(dst : nat, src : nat, size :nat ){
  MpnSameOrIncrP2(dst, size, src, size)
}

opaque predicate MpnSameOrIncrP2(dst : nat, dsize : nat, src : nat, ssize : nat) {
  (dst <= src) || !MpnOverlapP(dst, dsize, src, ssize)
}

opaque predicate MpnOverlapP(xp : nat, xsize : nat, yp : nat, ysize : nat) {
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

  var cy := mpn_add_n(heap, rp, up, vp, 4);

  print "These should still be 0, 4, 8\n";
  print "up ", up, "\n";
  print "vp ", vp, "\n";
  print "rp ", rp, "\n";

  print "heap ", heap[..], "\n";
  print "carry ", cy, "\n";

  print "16 * carry, plus the last 4 values from the heap (read in little-endian order), should be 24";
}
