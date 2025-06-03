include "pow2.dfy"

// Based on line 37 of https://github.com/gmp-mirror/gmp/blob/master/mpn/generic/add_n.c
// The pointers point to arrays of bits, but for an
// efficient version it should be something like array<bv64>
method mpn_add_n(heap: array<bv1>, rp: nat, up: nat, vp: nat, n: nat) returns (cy: bv1)
  modifies heap
  // TODO require that rp, rp + n, up, up + n, vp, vp + n are in-bounds for the heap
  // TODO ensure that the only part of the heap that could change is heap[rp..rp+n]
  // TODO Add these as requirements too:
  //  ASSERT (n >= 1);
  //  ASSERT (MPN_SAME_OR_INCR_P (rp, up, n));
  //  ASSERT (MPN_SAME_OR_INCR_P (rp, vp, n));
  // Note that the pointers are allowed to overlap as long as
  // it's "in a way suitable for an incrementing/decrementing algorithm";
  // see gmp/gmp-impl.h, line 2467
  ensures Pow2(n) * cy as nat + BitsToInt(heap[rp..rp+n]) ==
          BitsToInt(old(heap[up..up+n])) + BitsToInt(old(heap[vp..vp+n]))
{
  cy := 0;
  // Create mutable versions of these variables
  var rp' := rp;
  var up' := up;
  var vp' := vp;
  var n' := n;
  // The C code uses a do-while loop, so this while loop must execute at least once
  var first_time := true;
  while first_time || n != 0
  {
    first_time := false;
    var ul := heap[up'];
    up' := up' + 1;
    var vl := heap[vp'];
    vp' := vp' + 1;
    var sl := ul + vl;
    var cy1 := if sl < ul then 1 else 0;
    var rl := sl + cy;
    var cy2 := if rl < sl then 1 else 0;
    cy := cy1 | cy2;
    heap[rp'] := rl;
    rp' := rp + 1;
    n' := n-1;
  }

  return cy;
}

// TODO If the C code is little-endian,
// then this and the examples in Main
// need to be changed
ghost function BitsToInt(s: seq<bv1>): nat
{
  if |s| == 0 then  0  else  (2 * BitsToInt(s[0..|s|-1]) + s[|s|-1] as int)
}

method Main() {

  var heap := new bv1[] [1, 0, 1, 1, // 11
  1, 1, 0, 1, // 13
  0, 0, 0, 0];// empty memory to be filled in
  var up := 0;
  var vp := 4;
  var rp := 8;

  var cy := mpn_add_n(heap, rp, up, vp, 4);

  print "These should still be 0, 4, 8";
  print "up ", up;
  print "vp ", vp;
  print "rp ", rp;

  print "heap ", heap;
  print "carry ", cy;

}
