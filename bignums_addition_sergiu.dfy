method Main() {
    print "Examples:\n";

    var a := "1";  
    var b := "1";  

    a := normalizeBitString(a); // TODO: maybe do this in str2int
    b := normalizeBitString(b);
    print "a = ", a, " (decimal=", str2int(a), ")\n";
    print "b = ", b, " (decimal=", str2int(b), ")\n";

    var s := add(a, b);
    print "a + b = ", s, " (decimal=", str2int(a)+str2int(b), ")\n";
    print str2int(s);
}

method add(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    requires NormalizedBitString(s1) && NormalizedBitString(s2)
    ensures ValidBitString(res)
  //  ensures str2int(res) == str2int(s1) + str2int(s2)
{
    // We implement classic binary addition from right to left.
    // Step 1: Normalize inputs (drop leading zeros if needed).
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);
    // By postcondition of normalizeBitString, we have:
    assert str2int(x) == str2int(s1);
    assert str2int(y) == str2int(s2);

    var x': string; var y': string; var targetLen:int;
    x',y',targetLen := EnvelopeSameLength(x, y);
    // By postcondition of EnvelopeSameLength, we have:
    assert str2int(x') == str2int(x);
    assert str2int(y') == str2int(y);
    assert ValidBitString(x') && ValidBitString(y');
    assert targetLen == 2 + if |x| > |y| then |x| else |y|;
    assert |x'| == targetLen;
    assert |y'| == targetLen;

    assert str2int(s1) + str2int(s2) == str2int(x') + str2int(y');
   
    // If either is "0", the sum is the other.
    if x == "0" {
        assert str2int(x) == 0;
        res := y; return;
    }
    if y == "0" {
        assert str2int(y) == 0;
        res := x; return;
    }

    // We build the result from the least significant bit forward.
    var i := |x| - 1;  // index on x
    var j := |y| - 1;  // index on y
    var k := |x'|-1; // index on x',y' (proof envelopes)
   
    assert i >= 0 && j >= 0;
    
    var suffX := ""; var suffX' := ""; var x_old := ""; // substrings of x (or x')
    var suffY := "";  var suffY' := ""; var y_old := ""; // substrings of y (or y')
          
    var sumXY: string := ""; var sumXY_old := ""; // intermediate sum (of suffices)
    var sumXY_int: nat := 0; // intermediate sum in decimal
    assert str2int(sumXY_old) == str2int(x_old) + str2int(y_old);
  
    var carry := 0;
    var e:= 0; //exponent
    var sb: string := ""; // sequence of chars for result (in reverse order) //NOTE: changed to normal order for now
    assert e == |x'| - 1 - k && e == |y'| - 1 - k;
    assert |sumXY_old| == e; 
    assert k == |x'| - 1;
    assert k == (2 + if |x| > |y| then |x| else |y|) - 1;
    assert k == (2 + if  i > j then i else j) ;
    assert i >= 0 && j >= 0;
    assert k >=0; 
   
    while (i >= 0 || j >= 0 || carry != 0)  
        decreases (if i >= j then i else j) + 1, carry 
        invariant 0 <= carry <= 1
        invariant -1 <= i <= |x| - 1 && -1 <= j <= |y| - 1
        invariant k <= |x'| - 1 // for the proof strings
        invariant k <= |x'| - |x| + i
        invariant k <= |y'| - |y| + j
        invariant k == 1 ==> i < 0 && j < 0
        //invariant k == 0 ==> i < 0 && j < 0 && carry == 0
        invariant i >=0 ==> k == |x'| - |x| + i && k >= 2
        invariant j >=0 ==> k == |y'| - |y| + j && k >= 2
        invariant ValidBitString(sb)  
        invariant ValidBitString(sumXY) && ValidBitString(suffX) && ValidBitString(suffY)
        invariant ValidBitString(sumXY_old) && ValidBitString(x_old) && ValidBitString(y_old)
        invariant k == |x'| - 1 ==> x_old == "" && y_old == ""
        invariant k < |x'| - 1 ==> x_old == x'[k+1..|x'|] && y_old == y'[k+1..|y'|]
        invariant e == |x'| - 1 - k && e == |y'| - 1 - k
        invariant |sumXY_old| == e
      //  invariant k >= 0
        invariant str2int(x_old) + str2int(y_old) ==  carry * pow(2,e) + str2int(sumXY_old)
    {
       // assert (i >= 0 || j >= 0 || carry != 0) ==> k >= 0;
       /* ASSUMPTION 1 */ assume k >= 0; // TODO: need to prove this
        assert i <=|x|-1 && j <= |y| - 1; 
        assert |x'| == |y'|; 
        
        var bitX := 0; var bitX' := 0; 
        if i >= 0 {
            // TODO: also read the actual bitstring x
           // EnvLemma(x, x', i, k);
           // proof envelope bitstring 
           // bitX,suffX,suffX' := BitDecompositionFromIndex(x', k); 
        } 
        /*
        else {// proof bitstring  
                assert k >=0;assert k <= |x'| - 1; 
                bitX,suffX,suffX' := BitDecompositionFromIndex(x', k);
           /*     assert x' == x'[0..|x'|];
                assert ValidBitString(x');
                assert ValidBitString(x'[k..|x'|]);
                assert ValidBitString(x'[k..k+1]);
                assert bitX == str2int(x'[k..k+1]);
                assert k <= |x'| - |x|; 
                EnvLemma(x,x',k);
                assert x'[k..k+1] == "0";
                str2intLemma(x', k, |x'| - 1);
                assert str2int(x') == str2int(x'[k..k+1]) * pow(2, |x'| - 1 - k) + str2int(x'[k+1..|x'|]);
                assert str2int(x'[k+1..|x'|]) == str2int(x');
                assert str2int(x'[k..k+1]) * pow(2, |x'| - 1 - k) == 0;
                assert str2int(x'[k..k+1]) == 0;*/
                
                /* ASSUMPTION 2.1 */ assume bitX == 0; // TODO: need to prove this using code above 
        }  */
        //assert i < 0 ==> bitX == 0;
        bitX,suffX,suffX' := BitDecompositionFromIndex(x', k); 
        assert  k < |x'| - 1  ==> suffX == x'[k+1..|x'|] && suffX == x_old;
        assert  k < |x'| - 1 ==> str2int(x'[k..|x'|]) == bitX * pow(2, |x'| - 1 - k) + str2int(suffX);
            // base case
        assert k == |x'| - 1 ==> suffX == "" && suffX == x_old;
        assert k == |x'| - 1 ==> str2int(x'[k..|x'|]) == bitX * pow(2, 0) + str2int("");

        assert suffX == x_old;
        
        var bitY := 0; 
        if j >= 0 { // **
           // bitY, suffY, suffY' := BitDecompositionFromIndex(y', k);
        } /*else {
            // proof bitstring
            assert k >=0; assert k <= |y'| - 1;
            bitY, suffY, suffY' := BitDecompositionFromIndex(y', k);
          /*  assert y' == y'[0..|y'|];
            assert ValidBitString(y'[k..|y'|]);
            assert ValidBitString(y'[k..k+1]);
               
            assert bitY == str2int(y'[k..k+1]);

            assert k <= |y'| - |y|; 
            EnvLemma(y,y',k);
            assert y'[k..k+1] == "0";
            str2intLemma(y', k, |y'| - 1);
            assert str2int(y') == str2int(y'[k..k+1]) * pow(2, |y'| - 1 - k) + str2int(y'[k+1..|y'|]);
            assert str2int(y'[k+1..|y'|]) == str2int(y');
            assert str2int(y'[k..k+1]) * pow(2, |y'| - 1 - k) == 0;
            assert str2int(y'[k..k+1]) == 0;*/

            /* ASSUMPTION 2.2 */ assume bitY == 0; // TODO: need to prove this using code above 
        }*/
       // assert j < 0 ==> bitY == 0;
        bitY, suffY, suffY' := BitDecompositionFromIndex(y', k);

        assert k < |y'| - 1  ==> suffY == y'[k+1..|y'|] && suffY == y_old;
        assert k < |y'| - 1 ==> str2int(y'[k..|y'|]) == bitY * pow(2, |y'| - 1 - k) + str2int(suffY);
            // base case
        assert k == |y'| - 1 ==> suffY == "" && suffY == y_old;
        assert k == |y'| - 1 ==> str2int(y'[k..|y'|]) == bitY * pow(2, 0) + str2int("");

        assert suffY == y_old;
    
        assert |x'| == |y'|;
        assert e == |x'| - 1 - k && e == |y'| - 1 - k;
        assert str2int(x'[k..|x'|]) == bitX * pow(2, e) + str2int(suffX);
        assert str2int(y'[k..|y'|]) == bitY * pow(2, e) + str2int(suffY);
        Distributivity(str2int(x'[k..|x'|]), str2int(y'[k..|y'|]), bitX, bitY,e,str2int(suffX),str2int(suffY));    
        assert str2int(x'[k..|x'|]) + str2int(y'[k..|y'|]) ==  (bitX + bitY) * pow(2, e) + str2int(suffX) + str2int(suffY);
      
        var sum := bitX + bitY + carry;
        var old_carry := carry; 
        var digit := sum % 2;
        carry := sum / 2;
       // assert i < 0 && j < 0 ==> carry == 0;
       // assert k <= 1 ==> carry == 0;
        
        assert str2int(x_old) + str2int(y_old) == str2int(sumXY_old) + old_carry * pow(2,e); 
  
        var s_digit := if digit == 1 then "1" else "0";
        var s_carry := if carry == 1 then "1" else "0";
        var s_sum := s_carry + s_digit; 
        assert str2int(s_digit) == digit && str2int(s_carry) == carry;

        assert ValidBitString(s_digit) && ValidBitString(s_carry);
        ConcatPreservesValidBitString(s_carry, s_digit);
        assert ValidBitString(s_sum);
        str2intLemma(s_sum, 0, |s_sum| - 1);
        assert str2int(s_sum) == carry * pow(2, |s_sum| - 1) + digit;
        assert sum == str2int(s_sum);
      
        assert |sumXY_old| == e;

        var sumXY_new := s_digit + sumXY_old;
        assert |sumXY_new| == |s_digit| + |sumXY_old|;
        assert sumXY_new == s_digit + sumXY_old;
        assert |s_digit| == 1;
        assert sumXY_new[0..1] == s_digit;
        assert |sumXY_new| == 1 + |sumXY_old|;
        SubstringAfterConcat(s_digit, sumXY_old);
        assert sumXY_new[1..|sumXY_new|] == sumXY_old;
        str2intLemma(sumXY_new, 0, |sumXY_new| - 1);

        assert str2int(sumXY_new) == str2int(s_digit) * pow(2, |sumXY_new| - 1) + str2int(sumXY_old);
        assert |s_sum| - 1 + e == e + 1;
            
        assert |sumXY_new| == e+1;
        
        assert str2int(x'[k..|y'|]) + str2int(y'[k..|y'|]) ==  carry * pow(2, e+1) + str2int(sumXY_new);
         
        sumXY_old := sumXY_new; e := e + 1; k := k - 1;
        
        assert ValidBitString(y'[0..|y'|]);
        assert ValidBitString(x'[0..|x'|]); 

        assert k <=|x'|-1 && k <= |y'|-1; 

        assert ValidBitString(y'[k+1..|y'|]);
        assert ValidBitString(x'[k+1..|x'|]); 

        assert str2int(x'[k+1..|y'|]) + str2int(y'[k+1..|y'|]) ==  carry * pow(2, e) + str2int(sumXY_new);
          
        assert |sumXY_old| == e && e >= 0;
        assert str2int(x'[k+1..|x'|]) + str2int(y'[k+1..|y'|]) ==  carry * pow(2, e) + str2int(sumXY_old);
        x_old := x'[k+1..|x'|];
        y_old := y'[k+1..|y'|];
        
        if i >= 0 {
                i := i - 1; 
        }
            
        if j >= 0 {
                j := j - 1; 
        }

        assert str2int(x'[k+1..|x'|]) + str2int(y'[k+1..|y'|]) ==  carry * pow(2,e) + str2int(sumXY_old);
        assert str2int(x_old) + str2int(y_old) ==  carry * pow(2,e) + str2int(sumXY_old);
        assert e == |x'| - 1 - k && e == |y'| - 1 - k;
        assert |sumXY_old| == e;
   //     assert k == 1 ==> i < 0 && j < 0;
   //     assert (i >= 0 || j >= 0 || carry != 0) ==> k >= 0;
     }
   // assert x_old == x'[k+1..|x'|];
    assert k < |x'| - 1;
    assert k < |x'| - 1 ==> x_old == x'[k+1..|x'|] && y_old == y'[k+1..|y'|];
    assert x_old == x'[k+1..|x'|]; assert y_old == y'[k+1..|y'|];
    assert str2int(x_old) + str2int(y_old) ==  carry * pow(2,e) + str2int(sumXY_old);
    assert carry == 0;
    assert str2int(x'[k+1..|x'|]) + str2int(y'[k+1..|y'|]) ==  carry * pow(2, e) + str2int(sumXY_old);

    // NOTE: THIS IS THE MAIN RESULT OF THE LOOP; NEED TO CONNECT ALL TOGETHER TO CONCLUDE
    assert str2int(x'[k+1..|x'|]) + str2int(y'[k+1..|y'|]) ==  str2int(sumXY_old);

    assume 0 <= k; /* AGAIN ASSUMPTION 1*/ 
    assert k < |x'| - |x| && k < |x'|;
    assert |x'[k..|x'|]| == |x'| - k;
    assert ValidBitString(x) && ValidBitString(x');
    assert x'[|x'| - |x|..|x'|] == x;
    assert AllZero(x'[0..|x'| - |x|]); 
    assume k < |x|-1; /* ASSUMPTION 4 */ 
    assert |x'| - |x| < |x'| - k - 1;
    assert |x'| - |x| < |x'[k..|x'|]| - 1;
    
    EnvLemma(x,x',k);
   // assert x == x[0..|x|];
  //  assert x' == x'[0..|x'|];
    assume str2int(x'[k+1..|x'|]) == str2int(x); /*ASSUMPTION 5: should follow from EnvLemma for x,x' */
    assume str2int(y'[k+1..|y'|]) == str2int(y); /*ASSUMPTION 5: should follow from EnvLemma for y, y'*/
    
   // assert str2int(x) + str2int(y) == str2int(sumXY_old);
    // Reverse sb to get the proper bit string
    // TODO: no need to reverse, but maybe look at it later for sake of proof
   /* var rev := ""; 
    var k := |sb| - 1;
    while k >= 0
        decreases k
        invariant ValidBitString(rev)
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }
    assert ValidBitString(rev);
    res := normalizeBitString(rev);*/
    res := normalizeBitString(sb);
}

predicate GeneralCase(x: string, y: string, i: int, j: int)
{
    i >= 0 && j >= 0 && j < |y| - 1 && i < |x| - 1 && |x| - 1 - i == |y| - 1 - j
}


// ----------------------------------------------------
// 1) str2int: bit-string -> nat (reference function)
// ----------------------------------------------------
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

lemma str2intLemma(s: string, i: nat, n: nat)
    // bitstring decompostion of s_0...s_n after index i
    requires ValidBitString(s)
    requires n == |s| - 1
    requires 0 <= i <= n
    ensures str2int(s) == str2int(s[0..i+1]) * pow(2, n - i) + str2int(s[i+1..n+1])
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

method EnvelopeSameLength(x: string, y: string) returns (x': string, y': string, targetLen: int)    
  requires ValidBitString(x) && ValidBitString(y)
  requires |x| > 0 && |y| > 0
  ensures |x'| == targetLen 
  ensures |y'| == targetLen 
  ensures targetLen == 2 + if |x| > |y| then |x| else |y|
  ensures ValidBitString(x') && ValidBitString(y')
  ensures str2int(x') == str2int(x)
  ensures str2int(y') == str2int(y)
  ensures AllZero(x'[0..targetLen - |x|]) // == Zeros(targetLen - |x|)
  ensures AllZero(y'[0..targetLen - |y|]) // == Zeros(targetLen - |y|)
  ensures x'[targetLen - |x|..|x'|] == x
  ensures y'[targetLen - |y|..|y'|] == y
{
    targetLen := 2 + if |x| > |y| then |x| else |y|;
  var pad_x := targetLen - |x|;
  var pad_y := targetLen - |y|;
  var zeros_x := Zeros(pad_x);
  var zeros_y := Zeros(pad_y);
  x' := zeros_x + x;
  y' := zeros_y + y;
  assert ValidBitString(x');
  assert ValidBitString(y');
  assert x'[0..pad_x] == zeros_x;
  assert y'[0..pad_y] == zeros_y;
  assert x'[pad_x..|x'|] == x;
  assert y'[pad_y..|y'|] == y;
  str2intLemma(x', pad_x-1, |x'| - 1);
  str2intLemma(y', pad_y-1, |y'| - 1);
  assert |x| - 1 >= 0;
  assert |x'| - 1 - pad_x == |x| - 1;
  assert |y'| - 1 - pad_y == |y| - 1 >= 0;
  assert str2int(x') == str2int(zeros_x) * pow(2, |x'| - 1 - pad_x) + str2int(x);
  assert str2int(y') == str2int(zeros_y) * pow(2, |y'| - 1 - pad_y) + str2int(y);
  assert str2int(zeros_x) == 0;
  assert str2int(zeros_y) == 0;
  assert str2int(x') == 0 * pow(2, |x'| - 1 - pad_x) + str2int(x);
  assert str2int(y') == 0 * pow(2, |y'| - 1 - pad_y) + str2int(y);
  assert ValidBitString(x');
  assert ValidBitString(y');
 // assert str2int(x') == str2int(x[0..|x|]);
 // assert str2int(y') == str2int(y[0..|y|]);
  assert str2int(x') == str2int(x);
  assert str2int(y') == str2int(y);
  assert |x'| == targetLen;
  assert |y'| == targetLen;
  assert targetLen == 2 + if |x| > |y| then |x| else |y|;
  assert x'[0..pad_x] == zeros_x;
  assert y'[0..pad_y] == zeros_y;
  assert AllZero(zeros_x);
    assert AllZero(zeros_y);
  assert AllZero(x'[0..pad_x]);
  assert AllZero(y'[0..pad_y]);
  assert AllZero(x'[0..targetLen - |x|]);
  assert AllZero(y'[0..targetLen - |y|]);
  assert x'[targetLen - |x|..|x'|] == x;
  assert y'[targetLen - |y|..|y'|] == y;
}

// ----------------------------------------------------
// Helpers for string-based arithmetic
// ----------------------------------------------------

lemma NormalizedBitStringLemma(s: string)
    requires ValidBitString(s)
    requires NormalizedBitString(s)
    requires |s| > 1 // Only for strings longer than 1
    ensures NormalizedBitString(s[0..|s|-1])
{
    // If s is normalized and has length > 1, then s[0..|s|-1] is also normalized.
    // This is a lemma to help with the proof of str2int.
    assert ValidBitString(s[0..|s|-1]);
    if s == "0" || s == "1" {
        // s[0..|s|-1] == "" which is not a normalized bit string, but this case is excluded by |s| > 1
    } else {
        // s[0] == '1' and |s| > 1, so s[0..|s|-1] is still normalized
        assert |s[0..|s|-1]| > 0;
        assert s[0] == '1';
        assert NormalizedBitString(s[0..|s|-1]);
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

lemma SubstringAfterConcat(s: string, t: string)
  ensures (s + t)[|s|..|s + t|] == t
{
}


method ReadAtIndex(s: string, i: int) returns (s_i: string, s_i': string)
    requires ValidBitString(s) && 0 <= i < |s|
    ensures ValidBitString(s_i) && ValidBitString(s_i')
    ensures s_i == s[i..] && s_i' == s[i+1..] && |s_i|-1 >= 0   
    ensures str2int(s_i) == str2int(s[i..i+1]) * pow(2, |s_i|-1) + str2int(s_i') 
 {
    s_i := s[i..]; 
    s_i' := s[i+1..];
   
    assert |s_i|-1 >=0;
    assert s_i == s[i..i+1] + s[i+1..];
    assert s_i[0..1] == s[i..i+1];
    assert s_i[1..|s_i|] == s_i' || (|s_i| == 1 && s_i' == "");
        
    str2intLemma(s_i, 0, |s_i|-1);
   // postcondition
    assert str2int(s_i) == str2int(s[i..i+1]) * pow(2, |s_i|-1) + str2int(s_i');
}

// ----------------------------------------------------
// 2) int2str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
function int2str(n: nat): string
    decreases n
{
    if n == 0 then
        "0"
    else if n == 1 then
        "1"
    else
        int2str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

function pow(base: nat, exp: nat): nat
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

lemma EnvLemma(x: string, x': string, k: int)
    requires 0 <= k && k < |x'| - |x| && k < |x'|
    requires |x'| - |x| < |x'[k..|x'|]| - 1
    requires ValidBitString(x) && ValidBitString(x')
    requires x'[|x'| - |x|..|x'|] == x
    requires AllZero(x'[0..|x'| - |x|]) 
    ensures str2int(x'[k..|x'|]) == str2int(x)
    ensures x'[k..k+1] == "0"
{
    assert AllZero(x'[0..|x'| - |x|]);
    assert AllZero(x'[k..|x'| - |x|]);
    assert x'[k..k+1] == "0";
    
    assert ValidBitString(x'[k..|x'|]);
    assert 0 <= |x'|-|x|; 
    assert |x'|-|x| <= |x'[k..|x'|]| - 1;
    var s := x'[k..|x'|];
    var i := |x'| - |x| - k;
    str2intLemma(s, i, |s| - 1);

    assert str2int(s) == str2int(s[0..i+1]) * pow(2, |s| - 1 - i) + str2int(s[i+1..|s|]);

    assert s == x'[k..|x'|];
    assert |s| == |x'| - k;
    assert i == |x'| - |x| - k;
    assert |s| - 1 - i == |x| - 1;

    assert s[0..i+1] == x'[k..k+i+1];
    assert s[i+1..|s|] == x'[k+i+1..|x'|];


    assert str2int(x'[k..|x'|]) == str2int(x'[k..k+i+1]) * pow(2, |s| - 1 - i) + str2int(x'[k+i+1..|x'|]);
    /* ASUSMPTION 3, TO PROVE */assume str2int(x'[k..|x'|]) == str2int(x);
}


