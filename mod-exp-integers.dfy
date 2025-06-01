lemma ModuloDistributivityAdd_int(a: int, b: int, z: int)
  requires z > 0
  ensures (a + b) % z == ((a % z) + (b % z)) % z
{
 assume  (a + b) % z == ((a % z) + (b % z)) % z;
}

lemma ModuloDistributivityMul_int(x: int, y: int, z: int)
  requires z > 0
  ensures (x * y) % z == ((x % z) * (y % z)) % z
{
    assume (x * y) % z == ((x % z) * (y % z)) % z;
}


// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

lemma Exp_int_greater_than_0(x: nat, y: nat)
  requires x > 0
  ensures Exp_int(x, y) > 0
{
  reveal Exp_int();
  if y == 0 {
    return;
  } else {
    Exp_int_greater_than_0(x, y - 1); 
    return;
  }
}


lemma ExpDistributivity_int(x:nat, y1:int, y2:int) 
requires y1 >= 0 && y2 >= 0 
// NOTE: only positive exponents for now  
ensures Exp_int(x,y1+y2) == Exp_int(x,y1) * Exp_int(x,y2)
decreases y1 
{
    reveal Exp_int();
    if y1 == 0 {
        assert Exp_int(x,y1) == 1;
        assert y1 + y2 == y2; 
        assert Exp_int(x,y1+y2) == Exp_int(x,y2) * 1;
    } else 
    if y1 == 1 {
        assert Exp_int(x,y1) == x;
    } 
    else { 
        // applying induction
        assert y1 > 1; 
        assert y1 + y2 == 1 + ((y1 - 1) + y2);
        ExpDistributivity_int(x,1, (y1 - 1) + y2); 
        ExpDistributivity_int(x,y1 - 1, y2); 
    }
    
}

lemma ModExpDistributivity_int(x:nat, y1:int, y2:int, z:int) 
requires y1 >= 0 && y2 >= 0 && z > 0 
// NOTE: only positive exponents for now  
ensures Exp_int(x,y1+y2) % z == (Exp_int(x,y1) % z) * (Exp_int(x,y2) % z) % z
{
  ExpDistributivity_int(x,y1,y2); 
  assert Exp_int(x,y1+y2) == Exp_int(x,y1) * Exp_int(x,y2); 
  assert Exp_int(x,y1+y2) % z == (Exp_int(x,y1) * Exp_int(x,y2)) % z;
  ModuloDistributivityMul_int(Exp_int(x,y1),Exp_int(x,y2), z); 
  assert (Exp_int(x,y1) * Exp_int(x,y2)) % z ==  (Exp_int(x,y1) % z) * (Exp_int(x,y2) % z) % z;
}


// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n) 
  requires z > 0
  ensures res == Exp_int(x,y) % z 
  decreases n 
{
    reveal Exp_int();
    if n == 0 {
        res := Exp_int(x,1) % z;
        return;
    } 
    else {
        assert n > 0;
        var y' := Exp_int(2,n-1);
        var res' := ModExpPow2_int(x,y', n-1, z);
        res := (res' * res') % z; // squaring
        ModExpDistributivity_int(x,y',y',z); 
        return;
    }
}

// simulates the exponentiation we do on bistrings through bit decomposition and repeated squaring
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1) 
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z 
  decreases n 
{
  reveal Exp_int();
  
  Exp_int_greater_than_0(2,n);
  
  var first_bit := y / Exp_int(2,n);
  var remainder := y % Exp_int(2,n);
  var first_term := first_bit * Exp_int(2,n); 
  assert y == first_term + remainder;  

  if n == 0 { 
    assert y == 0 || y == 1; 
    if y == 0 { 
      assert Exp_int(x,y) == 1;
      assert 1 % z == 1;
      res := 1; 
      return;
      }
    else if y == 1 { 
      assert Exp_int(x,y) == x;
      res := x % z; 
      return;
    } 
  } else if first_term == 0 {
    assert n > 0;
    res := ModExp_int(x,remainder, n-1,z); 
    return;
  }
  else {
    ModExpDistributivity_int(x,first_term,remainder,z);
    assert Exp_int(x,y) % z == ((Exp_int(x,first_term) % z) * (Exp_int(x,remainder) % z)) % z; 
    var exp_first := ModExpPow2_int(x,first_term, n, z); 
    var exp_remainder := ModExp_int(x,remainder,n-1,z);
    res :=  (exp_first * exp_remainder) % z;
    return;
  } 
    
}