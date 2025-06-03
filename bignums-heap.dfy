// Based on line 37 of gmp/mpn/generic/add_n.c
method mpn_add_n(heap: array<bv64>, rp: nat, up: nat, vp: nat, n: nat) returns (cy: bv64)
{
  var i: nat := 0;
  cy := 0;

  while i < n
  {
    var ul := heap[up + i];
    var vl := heap[vp + i];
    var sl := ul + vl;
    var cy1 := if sl < ul then 1 else 0;
    var rl := sl + cy;
    var cy2 := if rl < sl then 1 else 0;
    cy := cy1 | cy2;
    heap[rp + i] := rl;
    i := i + 1;
  }

  return cy;
}
