
// ----------------------------------------------------
// 5) mul: string-based multiplication
//    No direct use of str2int/int2str
// ----------------------------------------------------
method mul(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s1) * str2int(s2)
{
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);
    assert str2int(x) == str2int(s1);
    assert str2int(y) == str2int(s2);
    assert str2int(s1) * str2int(s2) == str2int(x) * str2int(y);

    // If either is "0", result is "0"
    if x == "0" || y == "0" {
        res := "0";
        return;
    }

    // We'll implement the classic method:
    //   product = 0
    //   for each bit of y (from right to left):
    //       if that bit == 1, add (x << position) to product
    // Use add(...) to accumulate partial sums.

    var product := "0";
    var shiftCount := 0;
    var idx := |y| - 1;

    // checking initial conditions
    var partial_init := leftShift(x, shiftCount); 
    assert str2int(partial_init) == str2int(x) * pow(2, shiftCount);
    var currentSuffix := y[idx+1..|y|];
    assert str2int(product) == str2int(x) * str2int(currentSuffix);
    assert currentSuffix == y[idx+1..|y|];
    assert ValidBitString(currentSuffix);
    var bitY := y[idx];
    while idx >= 0
        decreases idx
        invariant ValidBitString(product) && ValidBitString(x) && ValidBitString(y)
        invariant 0 <= idx ==> ValidBitString(y[idx..|y|])
        invariant ValidBitString(y[idx+1..|y|])
        invariant idx == |y| - 1 - shiftCount
        invariant -1 <= idx <= |y| - 1
        invariant (bitY == '1' || bitY == '0') ==> idx >= 0 
        invariant str2int(product) == str2int(x) * str2int(y[idx+1..|y|])
        invariant ValidBitString(currentSuffix)
        invariant str2int(product) == str2int(x) * str2int(currentSuffix)
        invariant currentSuffix == y[idx+1..|y|]
    {
        assert ValidBitString(y[idx..|y|]);
        var result: int;
        if y[idx] == '1' {
            assert 0 <= idx;
       
            var partial := leftShift(x, shiftCount); // partial = x shifted by shiftCount
            assert str2int(partial) == str2int(x) * pow(2, shiftCount);
            assert ValidBitString(partial) && ValidBitString(product);

            product := add(product, partial);
            // by induction hypothes applied to previous value of product and definition of add(,)
            assert str2int(product) == str2int(partial) + str2int(x) * str2int(y[idx+1..|y|]);
            // by the definition of partial
            assert str2int(product) == str2int(x) * (pow(2, shiftCount) + str2int(y[idx+1..|y|]));

            // separating the first bit of y[idx..|y|] 
            str2intHeadTailLemma(y, idx);
            assert ValidBitString(y);
            assert shiftCount == |y| - 1 - idx;
            assert str2int(y[idx..|y|]) == pow(2, shiftCount) + str2int(y[idx+1..|y|]);

            assert str2int(product) == str2int(x) * str2int(y[idx..|y|]);
            result := str2int(product);

        } else { // y[idx] == '0'
            assert 0 <= idx;
            str2intHeadTailLemma(y, idx);
            assert shiftCount == |y| - 1 - idx;
            assert str2int(y[idx..|y|]) == str2int(y[idx+1..|y|]);

            assert str2int(product) == str2int(x) * str2int(y[idx..|y|]);
       
            result := str2int(product);
            }

        assert ValidBitString(y[idx+1..|y|]);
       
        assert result == str2int(x) * str2int(y[idx..|y|]);
        assert str2int(product) == str2int(x) * str2int(y[idx..|y|]);
        var old_idx := idx;
        assert str2int(product) == str2int(x) * str2int(y[old_idx..|y|]);
        shiftCount := shiftCount + 1;
        idx := idx - 1;
      
        if idx >= 0 {
            bitY := y[idx];
        } else {
            bitY := '.';
        }
        assert str2int(product) == str2int(x) * str2int(y[idx+1..|y|]);
        currentSuffix := y[idx + 1 .. |y|];
        assert str2int(product) == str2int(x) * str2int(currentSuffix);
        assert ValidBitString(currentSuffix);
    }
    assert idx == -1;
    assert ValidBitString(product);
    assert currentSuffix == y[0..|y|];
    assert currentSuffix == y;
    assert str2int(product) == str2int(x) * str2int(currentSuffix);
    assert str2int(currentSuffix) == str2int(y);
    assert str2int(product) == str2int(x) * str2int(y); 
    res := product;
    assert str2int(res) == str2int(x) * str2int(y); 
    assert str2int(x) == str2int(s1);
    assert str2int(y) == str2int(s2);
    assert str2int(s1) * str2int(s2) == str2int(x) * str2int(y);
    assert str2int(res) == str2int(s1) * str2int(s2);
}

lemma TermSubsitutionLemma(a:int, b:int, c:int, d:int, e:int)
    requires a == b * (e + d)
    requires c == e + d
    ensures a == b * c
{ }
 
lemma str2intHeadTailLemma(y: string, idx: int)
    requires 0 <= idx < |y|
    requires ValidBitString(y)
    ensures  ValidBitString(y[idx..|y|]) 
    ensures ValidBitString(y[idx..idx+1])
    ensures  ValidBitString(y[idx+1..|y|])
    ensures str2int(y[idx..|y|]) == str2int(y[idx..idx+1]) * pow(2, |y| - 1 - idx) + str2int(y[idx+1..|y|])

{
    var suff := y[idx..|y|];
    str2intLemma(suff, 0, |suff| - 1);
    assert str2int(suff) == str2int(suff[0..1]) * pow(2, |suff| - 1) + str2int(suff[1..|suff|]);
    assert suff == y[idx..|y|];
    assert |suff| == |y| - idx;
    assert suff[0..1] == y[idx..idx+1];
    assert suff[1..|suff|] == y[idx+1..|y|];
    assert str2int(y[idx..|y|]) == str2int(y[idx..idx+1]) * pow(2, |y| - 1 - idx) + str2int(y[idx+1..|y|]);
}


// ----------------------------------------------------
// Helper: leftShift - shift a bit string left by appending zeros
// ----------------------------------------------------

method leftShift(s: string, n: nat) returns (res: string)
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s) * pow(2,n)
{
    if s == "0" || n == 0 || |s| == 0 {
        res := s;
        return;
    }
    var zeros := "";
    var i := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant |zeros| == i
        invariant ValidBitString(zeros) && AllZero(zeros)        
    {
        zeros := zeros + "0";
        i := i + 1;
    }
    assert ValidBitString(zeros) && i == n && |zeros| == n;
    res := s + zeros;
    assert |res| == |s| + n;
    assert res[0..|s|] == s;
    assert res[|s|..|res|] == zeros;
    assert 1 <= |s|; 
    str2intLemma(res, |s|-1, |res| - 1);
    assert str2int(res) == str2int(s) * pow(2, n) + str2int(zeros);
    assert AllZero(zeros);
    TheZeroStringLemma(zeros);
    assert str2int(zeros) == 0;
    assert str2int(res) == str2int(s) * pow(2, n);
}

// ----------------------------------------------------
// 4) sub: string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method sub(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    requires str2int(s1) >= str2int(s2)
  //  ensures ValidBitString(res)
   // ensures str2int(res) == str2int(s1) - str2int(s2)
{
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);

    // If y == "0", the difference is x
    if y == "0" {
        res := x;
        return;
    }
    // If x == y, the difference is "0"
    if x == y {
        res := "0";
        return;
    }

    var i := |x| - 1; // pointer on x
    var j := |y| - 1; // pointer on y
    var borrow := 0;
    var sb := [];  // reversed result

    // proof variables
    var diffXY := ""; 
    var e := 0; 
    var valx: int := 0; 
    var valy: int := 0; 
    var valx_old: int := 0; 
    var valy_old: int := 0;
    var px := "0"+x;
    var py := "0"+y;
  //  assert px[i+1] == x[i];
  //  assert py[j+1] == y[j];
  //  assert px[0..1] == "0"; 
   // assert px[1..|px|] == x[0..|x|];
   // assert py[0..1] == "0"; 
   // assert py[1..|py|] == y[0..|y|];

    while i >= 0 || j >= 0
        decreases (if i >= j then i else j) + 1, borrow
        invariant 0 <= borrow <= 1
        invariant -1 <= i <= |x| - 1
        invariant -1 <= j <= |y| - 1
        invariant e >= 0
        invariant i >= 0 ==> |x| - 1 - i == e
        invariant j >= 0 ==> |y| - 1 - j == e
        invariant i >= 0 && j >= 0 ==> |x| - 1 - i == |y| - 1 - j
        invariant ValidBitString(x) && ValidBitString(y) 
        invariant ValidBitString(px[i+1..|px|]) && ValidBitString(py[j+1..|py|])
        invariant valx_old == str2int(px[i+2..|px|]) 
        invariant valy_old == str2int(py[j+2..|py|]) 
        invariant valx_old - valy_old == str2int(diffXY) - borrow * pow(2,e) 
        invariant |diffXY| == e;
       // invariant str2int(px[i+2..|px|]) - str2int(py[j+2..|py|]) == str2int(diffXY) - borrow * pow(2, e)
   
    {
       // assume str2int(px[i+2..|px|]) - str2int(py[j+2..|py|]) == str2int(diffXY) - borrow * pow(2, e);
        /* CODE */
        var bitX := 0;
        if i >= 0 {
            bitX := if x[i] == '1' then 1 else 0;
        }
        /* PROOF FOR STRUCTURE OF x[i..] == px[i+1..] */
        OneBitCorrect(px[i+1..i+2], bitX);
        assert bitX == str2int(px[i+1..i+2]);
      
        assert ValidBitString(px[i+1..|px|]);
        str2intHeadTailLemma(px,i+1);
        assert str2int(px[i+1..|px|]) == str2int(px[i+1..i+2]) * pow(2, |px| - 1 - (i+1)) + str2int(px[i+2..|px|]);
        assert |px| - 1 - (i+1) == |x| - 1 - i; 

        ghost var powx := pow(2, |x| - 1 - i);
        assert str2int(px[i+1..|px|]) == bitX * powx + str2int(px[i+2..|px|]);
        
        valx := str2int(px[i+1..|px|]); 
        assert valx == bitX * powx + str2int(px[i+2..|px|]);   
        assert valx == bitX * powx + valx_old;  

        valx_old := valx;     
        
        /* CODE */
        var bitY := 0;
        if j >= 0 {
            bitY := if y[j] == '1' then 1 else 0;
        }
        /* PROOF FOR STRUCTURE OF y[j..] == py[j+1..] */
        OneBitCorrect(py[j+1..j+2], bitY);
        assert bitY == str2int(py[j+1..j+2]);
      
        assert ValidBitString(py[j+1..|py|]);
        str2intHeadTailLemma(py,j+1);
        assert str2int(py[j+1..|py|]) == str2int(py[j+1..j+2]) * pow(2, |py| - 1 - (j+1)) + str2int(py[j+2..|py|]);
        assert |py| - 1 - (j+1) == |y| - 1 - j; 

        ghost var powy := pow(2, |y| - 1 - j);
        assert str2int(py[j+1..|py|]) == bitY * powy + str2int(py[j+2..|py|]);
        
        valy := str2int(py[j+1..|py|]); 
        assert valy == bitY * powy + str2int(py[j+2..|py|]);   
        assert valy == bitY * powy + valy_old;  

        valy_old := valy;     
        
        /* PROOF FOR STRUCTURE OF valx - valy */
        assert valx == bitX * powx + valx_old;  
        assert valy == bitY * powy + valy_old;  
        
        assert powx == powy || bitX == 0 || bitY == 0;
        DistributivityMinus(valx, valy, bitX, bitY,powx,powy,valx_old,valy_old);

        if i >= 0 { assert e == |x| - 1 - i;}
        else {assert e == |y|-1-j; }

        ghost var powe := pow(2,e);
        ghost var powe_new := pow(2,e+1);
        assert valx - valy == (bitX - bitY) * powe + valx_old - valy_old; 
 
        assert valx_old - valy_old == str2int(diffXY) - borrow * powe; 
        assert valx - valy == (bitX - bitY) * powe + str2int(diffXY) - borrow * powe; 
        assert valx - valy == (bitX - bitY) * powe - borrow * powe + str2int(diffXY); 
        assert valx - valy == (bitX - bitY - borrow) * powe + str2int(diffXY);  
        
        /* CODE */
        // Subtract with borrow:
        var diff := bitX - bitY - borrow;

        /* PROOF */
        var old_borrow := borrow;
        assert valx - valy == diff * powe + str2int(diffXY);  
        assert valx - valy == (diff+2) * powe - pow(2,e+1) + str2int(diffXY);  
         var new_diff := diff+2; var new_borrow := 1;
        if diff < 0 {
            // PROOF
            assert valx - valy == (diff+2) * powe - pow(2,e+1) + str2int(diffXY);  
            assert valx - valy == (diff+2) * powe - pow(2,e+1) + str2int(diffXY);  
            // CODE
            diff := diff + 2;
            borrow := 1;
            // PROOF
            assert diff == new_diff; assert borrow == new_borrow;            
            assert valx - valy == diff * powe - borrow*pow(2,e+1) + str2int(diffXY);  
        } else {
            // CODE
            borrow := 0;
            // PROOF
            assert borrow == 0;
            assert valx - valy == diff * powe + str2int(diffXY);  
            assert valx - valy == diff * powe - 0*pow(2,e+1) + str2int(diffXY);  
            assert valx - valy == diff * powe - borrow*pow(2,e+1) + str2int(diffXY);  
        }
        /* UPDATING THE EXPONENT FOR THE PROOF AT NEXT ITERATION */
        assert valx - valy == diff * powe - borrow*pow(2,e+1) + str2int(diffXY); 
        var new_e := e + 1;
        assert new_e == e + 1;
        assert valx - valy == diff * pow(2, new_e-1) - borrow*pow(2,new_e) + str2int(diffXY); 
        e := e + 1;
        assert e == new_e;
        assert valx - valy == diff * pow(2, e-1) - borrow*pow(2,e) + str2int(diffXY); 
        assert |diffXY| == e-1;
        var diffXY_new := "";

         /* CODE */
        if diff == 1 {
            sb := sb + ['1'];
        /* PROVE THE INVARIANT FOR sb RESP. diffXY */
            assert str2int("1") == diff;
            diffXY_new := "1"+diffXY;
      //      NewBit(diffXY_new, diffXY, "1", diff, e-1);
            assert str2int(diffXY_new[0..1]) == diff;
            assert diffXY_new[0..1] == "1";
            assert diffXY_new[1..|diffXY_new|] == diffXY;
            assert |diffXY_new| == e;
            str2intLemma(diffXY_new,0,e-1);
            assert str2int(diffXY_new[0..e]) == str2int(diffXY_new[0..1]) * pow(2,e-1) + str2int(diffXY_new[1..e]);
            assert str2int(diffXY_new[0..1]) == diff; 
            assert str2int(diffXY_new) == diff * pow(2,e-1) + str2int(diffXY);
        /* TODO: RELATE sb TO diffXY */
        }
        else{ assert diff == 0;
            /* CODE */
            sb := sb + ['0'];
            /* PROVE THE INVARIANT FOR sb RESP. diffXY */
            assert str2int("0") == diff;
            diffXY_new := "0"+diffXY;
          //  NewBit(diffXY_new, diffXY, "1", diff, e-1);
            
            assert str2int(diffXY_new[0..1]) == diff;
            assert diffXY_new[0..1] == "0";
            assert diffXY_new[1..|diffXY_new|] == diffXY;
            assert |diffXY_new| == e;
            assert str2int(diffXY_new[0..1]) == diff;
            assert ValidBitString(diffXY_new);
            str2intLemma(diffXY_new,0,e-1);
            assert diffXY_new == diffXY_new[0..e];
            assert str2int(diffXY_new[0..e]) == str2int(diffXY_new[0..1]) * pow(2,e-1) + str2int(diffXY_new[1..e]);

            assert str2int(diffXY_new) == diff * pow(2,e-1) + str2int(diffXY); 
        /* TODO: RELATE sb TO diffXY */
        }
        /* PROOF: FINAL ASSERTIONS AND UPDATES FOR NEXT ITERATION*/
        assert str2int(diffXY_new) == str2int(diffXY_new[0..1]) * pow(2,e-1) + str2int(diffXY_new[1..e]);
        assert valx - valy == diff * pow(2, e-1) - borrow*pow(2,e) + str2int(diffXY); 
        assert valx - valy == str2int(diffXY_new) - borrow * pow(2, e);
        valx_old := valx; valy_old := valy;
        diffXY := diffXY_new;
        assert ValidBitString(diffXY_new); assert ValidBitString(diffXY);
        assert valx_old == valx; assert valy_old == valy; assert diffXY == diffXY_new;
        assert valx_old - valy_old == valx - valy; 
        assert valx_old - valy_old == str2int(diffXY) - borrow * pow(2, e);
        //assert i >= 0 && j >= 0 ==> |x| - 1 - i == |y| - 1 - j;   
 
        /* CODE */
        if i >= 0 { i := i - 1; }
        if j >= 0 { j := j - 1; }
    }

    // Reverse result
    var rev := "";
    var k := |sb| - 1;
    while k >= 0
        decreases k
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }

    res := ""; //normalizeBitString(rev);
}

 /*lemma NewBitLemma(s':string, s:string, bit:string,ibit:int, e:int) 
    requires s' == bit+s
    requires str2int(bit) == ibit
    requires e == |s'|
    ensures str2int(s') == ibit * pow(2,e-1) + str2int(s)
 {
    

 }*/


lemma DistributivityMinus(x: int, y: int, x': int, y': int, z1:nat, z2:nat, a:int, b:int)
  requires x == x' * z1 + a
  requires y == y' * z2 + b
  requires z1 == z2 || x' == 0 || y' == 0
  ensures z1 == z2 || y'==0 ==> x - y == (x' - y') * z1 + a - b   
  ensures x' == 0 ==> x - y == (x' - y') * z2 + a - b
{
    if z1 == z2 {
        assert x - y == (x' - y') * z1 + a - b; }
    else if x' == 0 
    {  assert y == y' * z2 + b; assert x == a;
        assert x - y == a - (y' * z2 + b); 
        assert x - y == a - b - y' * z2; }
    else if y' == 0 
    { assert x == x' * z1 + a; assert y == b;
        assert x - y == (x' * z1 + a) - b; 
        assert x - y == (x' * z1 + a) - b; 
        assert x - y == x' * z1 + a - b;  }
} 


lemma OneBitCorrect(s: seq<char>, bit: int)
  requires ValidBitString(s)
  requires |s| == 1
  requires bit == if s[0] == '1' then 1 else 0
  ensures str2int(s) == if s[0] == '1' then 1 else 0
  ensures str2int(s) == bit
{
    assert s == s[0..1];
    assert ValidBitString(s);
    assert str2int(s) == str2int(s[0..1]); 
    assert str2int(s) == bit; 
    assert str2int(s) == if s[0] == '1' then 1 else 0;
}

// ----------------------------------------------------
// 3) add: string-based addition (no str2int / int2str)
// ----------------------------------------------------
method add(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s1) + str2int(s2)
{
    // We implement classic binary addition from right to left.
    // Step 1: Normalize inputs (drop leading zeros if needed).
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);

    // If either is "0", the sum is the other.
    if x == "0" {
        res := y;
        return;
    }
    if y == "0" {
        res := x;
        return;
    }

    // We build the result from the least significant bit forward.
    var i := |x| - 1;  // index on x
    var j := |y| - 1;  // index on y
    var carry := 0;
    var sb := []; // sequence of chars for result (in reverse order)

    while i >= 0 || j >= 0 || carry != 0
        decreases (if i >= j then i else j) + 1, carry
        invariant 0 <= carry <= 1
        invariant i <= |x| - 1 && j <= |y| - 1
    {
        var bitX := 0;
        if i >= 0 {
            bitX := if x[i] == '1' then 1 else 0;}
        var bitY := 0;
        if j >= 0 {
            bitY := if y[j] == '1' then 1 else 0;}

        var sum := bitX + bitY + carry;
        var digit := sum % 2;
        carry := sum / 2;


        if digit == 1 {
            sb := sb + ['1'];
        } else {
            sb := sb + ['0'];
        }

        if i >= 0 { i := i - 1; }
        if j >= 0 { j := j - 1; }
    }

    // Reverse sb to get the proper bit string
    var rev := "";
    var k := |sb| - 1;

    // ValidBitSequence(sb); 
 
    while k >= 0
        decreases k
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }
    // ValidBitSequence(sb, rev); 
        
    assume ValidBitString(rev);
    res := normalizeBitString(rev);
    assume str2int(res) == str2int(s1) + str2int(s2); 
    
}

function pow(base: nat, exp: nat): nat
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

// ----------------------------------------------------
// 3) helper functions and lemmas 
// ----------------------------------------------------

method normalizeBitString(s: string) returns(res: string)
    // Remove leading zeros, except keep at least one digit
    requires ValidBitString(s) // NOTE: needed to add this precondition
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s) // NOTE: added this useful postcondition 
    ensures NormalizedBitString(res)
    decreases s
{
    if AllZero(s) {         
        TheZeroStringLemma(s);
        return "0"; 
    } 
    else if s[0]=='1' { 
        return s; // already normalized
    }    
    else {
        var firstOne := FirstOne(s);
        assert firstOne > 0;
        var zero_prefix := s[0..firstOne];  
        var s_normalized := s[firstOne..|s|]; 
        assert AllZero(zero_prefix); 
        assert s == zero_prefix + s_normalized;
      
        TheZeroStringLemma(zero_prefix); 
        // implies str2int(zero_prefix) == 0; 
        str2intLemma(s, firstOne-1, |s| - 1); 
        // implies str2int(s) == str2int(zero_prefix) * pow(2, |s| - firstOne) + str2int(s_normalized);
        
        assert str2int(s[firstOne..|s|]) == str2int(s); // the postcondition
        return s_normalized;
        }
}

method FirstOne(s: string) returns (firstOne: int)
  requires ValidBitString(s)
  requires exists i :: 0 <= i < |s| && s[i] == '1'
  ensures 0 <= firstOne < |s| && s[firstOne] == '1'
  ensures AllZero(s[0..firstOne])
{
  var i := 0;
  while i < |s| && s[i] == '0'
    invariant 0 <= i <= |s|
    invariant AllZero(s[0..i]) //forall j :: 0 <= j < i ==> s[j] != '1'
  {
    i := i + 1;
  }
  firstOne := i;
}


predicate ValidBitString(s: string)
{
    // All characters must be '0' or '1'.
    forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

lemma ValidBitStringSlice(s: string, start: int, end: int)
  requires ValidBitString(s)
  requires 0 <= start <= end <= |s|
  ensures ValidBitString(s[start..end])
{
  // Need to show every character in s[start..end] is '0' or '1'
  forall i | 0 <= i < end - start
    ensures s[start..end][i] == '0' || s[start..end][i] == '1'
  {
    assert start + i < |s|;
    assert s[start + i] == '0' || s[start + i] == '1'; // from ValidBitString(s)
    assert s[start..end][i] == s[start + i];
  }
}

function char2int(c: char): nat
    requires c == '0' || c == '1'
{
    if c == '0' then 0 else 1
}

function str2int(s: string): nat
    requires ValidBitString(s) || |s| == 0
    decreases s
{
    if |s| == 0 then 0
    else 2 * str2int(s[0..|s|-1]) + char2int(s[|s|-1])
}

function str2intMSB(s: string): nat
    requires ValidBitString(s) || |s| == 0
    decreases s
{
    if |s| == 0 then 0
    else str2int(s[0..1]) * pow(2, |s| - 1) + str2int(s[1..])
}





lemma str2intLemma(s: string, i: nat, n: nat)
    // bitstring decompostion of s_0...s_n after index i
    requires ValidBitString(s)
    requires n == |s| - 1
    requires 0 <= i <= n
    ensures str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + str2int(s[i+1..n+1])
    ensures ValidBitString(s[0..i+1])
    ensures ValidBitString(s[i+1..n+1])
{
assert s == s[0..n+1];
if |s| == 0 || s == "0" {
    // These assertions speed up the proof
    assert str2int(s) == 0;
    assert ValidBitString(s[0..i+1]) && ValidBitString(s[i+1..n+1]);
    assert str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + str2int(s[i+1..n+1]);
} else if s == "1" {
    assert str2int(s) == 1;
    assert str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + str2int(s[i+1..n+1]);
} else if i == n {
    // s[0..i+1] == s and s[i+1..n+1] == ""
    assert str2int(s) == str2int(s[0..n+1]);
    assert str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + str2int(s[i+1..n+1]);
} else {    
    assert i < n;
    
    // Inductive step: apply lemma to the prefix s[0..n]
    var prefix: string := s[0..n];
    assert ValidBitString(prefix);
    str2intLemma(prefix, i, n - 1);
    
    // The induction hypothesis ensures:
    // str2int(prefix) == str2int(s[0..i+1]) * pow(2, (n-1) - i) + str2int(s[i+1..n])
    assert prefix == prefix[0..n];
    assert ValidBitString(prefix[i+1..n]);
    assert str2int(prefix[0..n]) == str2int(prefix[0..i+1]) * pow(2, (n-1) - i) + str2int(prefix[i+1..n]); // justified by lemma postcondition
    
    // By definition: str2int(s) = 2 * str2int(prefix) + char2int(s[n])
    assert prefix + s[n..n+1] == s[0..n+1];
    assert str2int(s) == 2 * str2int(prefix) + char2int(s[n]);
    assert str2int(s) == 2 * (str2int(prefix[0..i+1]) * pow(2, (n-1) - i) + str2int(prefix[i+1..n])) + char2int(s[n]);
    assert s[0..i+1] == prefix[0..i+1] && s[i+1..n] == prefix[i+1..n];
    assert str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + 2 * str2int(s[i+1..n]) + char2int(s[n]);
    
    // By definition: str2int(s[i+1..n+1]) = 2 * str2int(s[i+1..n]) + char2int(s[n])
    assert |s[i+1..n+1]| > 0;
    assert s[i+1..n+1] == s[i+1..n] + s[n..n+1]; 
    assert str2int(s[i+1..n+1]) == 2 * str2int(s[i+1..n]) + char2int(s[n]);
    assert str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + str2int(s[i+1..n+1]);
}
}


predicate AllZero(s: string)
{
    |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma TheZeroStringLemma(s:string)
    requires AllZero(s)
    ensures str2int(s) == 0
    {
    // If all characters are '0', then the integer value is 0.
    assert ValidBitString(s);
    assert AllZero(s);
    assert str2int(s) == 0;
    }

// True iff s is a valid bit string with no leading zeros (except "0" itself)
predicate NormalizedBitString(s: string)
{
    ValidBitString(s) && ( s == "0" || s == "1" || (|s| > 0 && s[0] == '1')
)
}



method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures str2int(s) == 0 
  ensures AllZero(s)
{
  if n == 0 {
    assert str2int("")==0; s :="";
  } 
  else {
    var st := Zeros(n - 1);
    assert ValidBitString(st);   
    assert str2int(st) == 0;
    assert |st| == n - 1;
    s := "0" + st;
    assert ValidBitString(s);
    assert s[0] == '0';
    assert s[1..|s|] == st;
    str2intLemma(s, 0, |s| - 1);
    assert str2int(s) == str2int("0") * pow(2, |s| - 1) + str2int(st);
    assert str2int(s) == 0 * pow(2, |s| - 1) + str2int(st); 
    assert str2int(s) == str2int(st);
    assert str2int(s) == 0;
    assert AllZero(s);
    }
}

method BitDecompositionFromIndex(x: string, i: int) returns (bitX: int, suffX:string, suffX':string)
    requires ValidBitString(x)
    requires 0 <= i <= |x| - 1
    ensures bitX == 0 || bitX == 1
    ensures i < |x| - 2  ==> suffX == x[i+1..|x|] && suffX' == x[i+2..|x|]
    ensures i == |x| - 2  ==> suffX == x[i+1..|x|] && suffX' == ""
    ensures i == |x| - 1  ==> suffX == "" && suffX' == ""
    ensures ValidBitString(x[i..|x|]) && ValidBitString(suffX)
    ensures str2int(x[i..|x|]) == bitX * pow(2, |x|-1-i) + str2int(suffX)
    ensures i < |x| - 1 ==> ValidBitString(x[i+1..|x|])
    ensures bitX == str2int(x[i..i+1])
{
    var len_xi := |x| - i; 
    bitX := str2int(x[i..i+1]); //if x[i] == '1' then 1 else 0;
    if i < |x| - 2 
    { suffX := x[i+1..|x|]; suffX' := x[i+2..|x|]; }
    else if i == |x| - 2 
    { suffX := x[i+1..|x|]; suffX' := ""; }
    else { 
        assert i == |x| - 1;
        suffX := ""; suffX' := "";
        assert x[i..|x|] == x[i..i+1]; 
    }
    var x_tail := x[i..|x|];
    // Assertions for applying the lemma
    assert ValidBitString(x[i..|x|]) && i < |x|;
    assert ValidBitString(x_tail);
    assert |x_tail| > 0;
    assert |x[i..|x|]| == len_xi == |x| - i == len_xi &&  |x[i..i+1]| == 1;
                 
    str2intLemma(x_tail, 0, |x_tail| - 1);
    if i == |x| - 1   {
        assert str2int(x[i..|x|]) == bitX * pow(2, 0) + str2int("");
        assert str2int(x[i..|x|]) == bitX * pow(2, 0) + str2int(suffX);
    }
    if i < |x| - 2 || i == |x| - 2 {
    // Assertions for using the conclusions of the lemma
        assert x_tail[0..1] == x[i..i+1];
        assert x_tail[1..] == x[i+1..|x|];
        assert x_tail == x_tail[0..|x_tail|];
        assert str2int(x_tail) == str2int(x_tail[0..1]) * pow(2, |x_tail|-1) + str2int(x_tail[1..]);
        assert str2int(x[i..|x|]) == bitX * pow(2, len_xi - 1) + str2int(x[i+1..|x|]);
        assert suffX == x[i+1..|x|];
        assert str2int(x[i..|x|]) == bitX * pow(2, len_xi - 1) + str2int(suffX);
        }
}

lemma Distributivity(x: int, y: int, bitX: int, bitY: int, e:nat, a:int, b:int)
  requires x == bitX * pow(2, e) + a
  requires y == bitY * pow(2, e) + b
  ensures x + y == (bitX + bitY) * pow(2, e) + a + b         
{
}


lemma SubstringAfterConcat(s: string, t: string)
  ensures (s + t)[|s|..|s + t|] == t
{
}

lemma ConcatPreservesValidBitString(s1: string, s2: string)
    requires ValidBitString(s1)
    requires ValidBitString(s2)
    ensures ValidBitString(s1 + s2)
{
    // Prove that for every character in s1 + s2, it is either '0' or '1'
    var s := s1 + s2;
    forall i | 0 <= i < |s| 
        ensures s[i] == '0' || s[i] == '1'
    {
        if i < |s1| {
            // Index falls within s1
            assert s[i] == s1[i]; // s = s1 + s2, so this holds
            assert s1[i] == '0' || s1[i] == '1'; // by ValidBitString(s1)
        } else {
            // Index falls within s2
            var j := i - |s1|;
            assert s[i] == s2[j]; // because s = s1 + s2
            assert s2[j] == '0' || s2[j] == '1'; // by ValidBitString(s2)
        }
    }
}

method int2str(n: nat) returns(s: string)
    decreases n
{ 
    if n == 0 {
        s:="0";}
    else if n == 1 {
        s:="1";}
    else 
    {
        // Recursively build from most significant bits.
        // The last character added is (n % 2).
        s:= int2str(n / 2); s:=s + (if n % 2 == 0 then "0" else "1");
    }
}