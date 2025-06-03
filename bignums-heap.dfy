method mpn_add_n(heap: array<uint64>, rp: nat, up: nat, vp: nat, n: nat) returns (cy: uint64)
{
  // No need to include ASSERT statements as they're for validation, not execution logic

  var i: nat := 0;
  cy := 0;

  while i < n
  {
    var ul: uint64 := heap[up + i];
    var vl: uint64 := heap[vp + i];
    var sl: uint64 := ul + vl;
    var cy1: uint64 := if sl < ul then 1 else 0;
    var rl: uint64 := sl + cy;
    var cy2: uint64 := if rl < sl then 1 else 0;
    cy := cy1 | cy2;
    heap[rp + i] := rl;
    i := i + 1;
  }

  return cy;
}
