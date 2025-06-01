include "bignums.dfy"
include "division.dfy"
include "mod-exp-integers.dfy"
include "bitstring-lemmas.dfy"

// computes (sx^sy) % sz for bitstrings sx,sy,sz when str2int(sy) == 2^n 
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1 
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n 
{
    reveal Exp_int();
    if Str2Int(sy) == 0 {
      res := "1";
      return;
    }
    else if n == 0 {
        var quotient,remainder := DivMod(sx, sz);
        res := remainder;
        return;
    } 
    else {
      // CODE
        var sy' := sy[..|sy|-1]; 
        var sy_sum := Add(sy',sy');
        var res' := ModExpPow2(sx,sy', n-1, sz);
        res := Mul(res',res'); // squaring
      // PROOF
        assert n > 0; assert |sy| > 1;
        assert Str2Int(sy) == Exp_int(2,n);
        Str2IntLemma(sy,|sy|-2);
        assert Str2Int(sy[|sy|-1..|sy|]) == 0; 
        assert Str2Int(sy) == Str2Int(sy') * Exp_int(2,1) + Str2Int(sy[|sy|-1..|sy|]);
        assert Str2Int(sy') == Exp_int(2,n-1);
        assert Str2Int(sy) == Str2Int(sy_sum);
        assert Str2Int(res') ==  Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz);
        assert Str2Int(res) == (Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz)); 

      // CODE  
        var quotient, remainder := DivMod(res, sz);
        res := remainder;
      // PROOF 
        assert Str2Int(res) == ((Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Str2Int(sy')) % Str2Int(sz))) % Str2Int(sz); 
        ModExpDistributivity_int(Str2Int(sx),Str2Int(sy'),Str2Int(sy'),Str2Int(sz)); 
        assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
        return;
      }

}

// computes (s1^s2) % s3 for bitstrings s1,s2,s3
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1) 
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy| 
{
  var n := |sy|;
  var zero_tail := Zeros(n-1); 
  var first_term := sy[..1]+zero_tail;
  var second_term := sy[1..]; 
 
  Str2IntLemma(sy,0);
  Str2IntLemma(first_term,0); 

  
  if |sy| == 1 {
    assert Str2Int(sy) == Str2Int(first_term);
    res := ModExpPow2(sx,sy,n-1,sz);
    return;
  } 
  else {
  // CODE
    var sy_sum := Add(first_term,second_term); 
    var first_res := ModExpPow2(sx,first_term,n-1,sz); 
    var second_res := ModExp(sx,second_term,sz);
    var plain_res := Mul(first_res,second_res); 
    // NOTE: do we need modular multiplication to keep strings as short as possible ? 
    var remainder,quotient := DivMod(plain_res,sz); 
    res := quotient;
  // PROOF
    assert Str2Int(res) == ( Str2Int(first_res) * Str2Int(second_res) ) % Str2Int(sz);
    ghost var x := Str2Int(sx); 
    ghost var y1,y2 := Str2Int(first_term), Str2Int(second_term); 
    ghost var z := Str2Int(sz); 
    
    assert Str2Int(sy_sum) == Str2Int(sy) == y1 + y2; //Str2Int(first_term) + Str2Int(second_term);
    assert Str2Int(first_res) == Exp_int(x,y1) % z;   
    assert Str2Int(second_res) == Exp_int(x,y2) % z; 
    assert Exp_int(x,Str2Int(sy)) % z ==  Exp_int(x,y1+y2) % z; 
    ModExpDistributivity_int(x,y1, y2,z);
    assert Exp_int(x,y1+y2) % z == (Exp_int(x,y1) % z) * (Exp_int(x,y2) % z) % z;
    assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    return;
  }

}
    

