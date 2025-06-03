include "bignums.dfy"

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

ghost function BitsToInt(s: seq<bv1>): nat
{
  if |s| == 0 then  0  else  (2 * BitsToInt(s[0..|s|-1]) + s[|s|-1] as int)
}
