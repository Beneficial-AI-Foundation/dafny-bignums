include "bignums.dfy"
// Based on line 37 of gmp/mpn/generic/add_n.c
// The pointers point to arrays of bits, but for an
// efficient version it should be something like array<bv64>
method mpn_add_n(heap: array<bv1>, rp: nat, up: nat, vp: nat, n: nat) returns (cy: bv1)
modifies heap
ensures Pow2(n) * cy as nat + BitsToInt(heap[rp..rp+n]) ==
        BitsToInt(heap[up..up+n]) + BitsToInt(heap[vp..vp+n])
{
  cy := 0;
  // mutable versions of these variables
  var rp' := rp;
  var up' := up;
  var vp' := vp;
  var n' := n;
  // simulate a do-while loop
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

function BitsToInt(s: seq<bv1>): nat
{
  if |s| == 0 then  0  else  (2 * BitsToInt(s[0..|s|-1]) + s[|s|-1] as int)
}
