include "bignums-lemmas.dfy"
// Helper lemma for maintaining the loop invariant in Mul
lemma MulAux(x: string, y: string, prevProduct: string, product: string,
             prevShift: string, shift: string, idx: int)
  requires ValidBitString(x) && ValidBitString(y)
  requires ValidBitString(prevProduct) && ValidBitString(product)
  requires ValidBitString(prevShift) && ValidBitString(shift)
  requires -1 <= idx < |y| - 1
  requires forall i :: 0 <= i < |prevShift| ==> prevShift[i] == '0'
  requires forall i :: 0 <= i < |shift| ==> shift[i] == '0'
  requires shift == prevShift + ['0']
  requires idx + 1 < |y|
  requires y[idx+1] == '0' ==> prevProduct == product
  requires y[idx+1] == '1' ==> OStr2Int(product) == OStr2Int(prevProduct)+ OStr2Int(x + prevShift)
  requires OStr2Int(x) * OStr2Int(y) == OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift)
  ensures OStr2Int(x) * OStr2Int(y) ==
          OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift) ==>
            OStr2Int(x) * OStr2Int(y) ==
            OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift)
{
  if y[idx+1] == '0' {
    calc {
      OStr2Int(x) * OStr2Int(y);
    ==
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift);
    ==
      {
        assert prevProduct == product;
        assert y[..idx+2] + prevShift == y[..idx+1] + shift;
      }
      OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
    }
  }
  else {
    var a := |shift|;
    calc {
      OStr2Int(x) * OStr2Int(y);
    ==
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+2] + prevShift);
    ==
      { assert y[..idx+2] + prevShift == y[..idx+1] + "1" + prevShift;}
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift);
    ==
      { TrailingZeros(y[..idx+1] + "1" + prevShift, a-1);
        assert OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(y[..idx+1] + "1") * Pow2(a-1) by {reveal OStr2Int;}
        assert OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(x) * (OStr2Int(y[..idx+1] + "1") * Pow2(a-1));
        assert OStr2Int(x) * (OStr2Int(y[..idx+1] + "1") * Pow2(a-1)) == OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1)
        by {MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1] + "1"), Pow2(a-1));}

        assert OStr2Int(x) * OStr2Int(y[..idx+1] + "1" + prevShift) == OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1);
      }
      OStr2Int(prevProduct) + OStr2Int(x) * OStr2Int(y[..idx+1] + "1") * Pow2(a-1);
    ==
      {reveal OStr2Int;
      }
      OStr2Int(prevProduct) + OStr2Int(x) * (2*OStr2Int(y[..idx+1]) + 1) * Pow2(a-1);
    ==
      {
        Expand(OStr2Int(x), 2*OStr2Int(y[..idx+1]), Pow2(a-1));
      }
      OStr2Int(prevProduct) + OStr2Int(x) * Pow2(a-1) + OStr2Int(x) * (2*OStr2Int(y[..idx+1])) * Pow2(a-1);
    ==
      {assert OStr2Int(x) * Pow2(a-1) == OStr2Int(x + prevShift) by {

         reveal OStr2Int;
         TrailingZeros(x+ prevShift, a-1);
       }
       calc {
         OStr2Int(x) * (2*OStr2Int(y[..idx+1])) * Pow2(a-1);
       ==
         {
           MulIsAssociative(OStr2Int(x), 2*OStr2Int(y[..idx+1]), Pow2(a-1));
         }
         OStr2Int(x) * ((2*OStr2Int(y[..idx+1])) * Pow2(a-1));
       ==
         {
           assert (2*OStr2Int(y[..idx+1])) * Pow2(a-1) == OStr2Int(y[..idx+1]) * Pow2(a)
           by{
             Pow2Inductive(a-1);
           }
         }
         OStr2Int(x) * (OStr2Int(y[..idx+1]) * Pow2(a));
       ==
         {MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1]), Pow2(a));}
         OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a);
       }
      }
      OStr2Int(prevProduct) + OStr2Int(x + prevShift) + OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a);
    ==
      {
        assert OStr2Int(y[..idx+1]) * Pow2(a) ==  OStr2Int(y[..idx+1] + shift) by {
          reveal OStr2Int;
          TrailingZeros(y[..idx+1] + shift, a);
        }
        MulIsAssociative(OStr2Int(x), OStr2Int(y[..idx+1]), Pow2(a));
        assert OStr2Int(x) * OStr2Int(y[..idx+1]) * Pow2(a) ==  OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
      }
      OStr2Int(prevProduct) + OStr2Int(x + prevShift) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
    ==
      {reveal OStr2Int;}
      OStr2Int(product) + OStr2Int(x) * OStr2Int(y[..idx+1] + shift);
    }
  }
}
