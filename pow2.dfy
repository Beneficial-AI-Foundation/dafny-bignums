
// This function will be useful in proofs
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Establish some properties of Pow2
lemma Pow2Zero()
  ensures Pow2(0) == 1
{
  reveal Pow2();
}

lemma Pow2Positive(n:nat)
  ensures Pow2(n) > 0
{
  if n == 0 {
    Pow2Zero();
  }
  else {
    Pow2Positive(n-1);
    reveal Pow2();
  }
}

lemma Pow2Inductive(i: nat)
  ensures Pow2(i+1) == 2*Pow2(i)
{
  reveal Pow2();
}
