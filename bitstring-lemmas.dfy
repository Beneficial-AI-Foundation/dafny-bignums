include "bitstrings.dfy"
include "mod-exp-integers.dfy"

function char2int(c: char): nat
  requires c == '0' || c == '1'
{
  if c == '0' then 0 else 1
}

lemma Str2IntLemmaAux(s: string, i: nat)
  requires ValidBitString(s)
  // requires n == |s| - 1
  requires 0 <= i <= |s|-1
  ensures OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..])
{
  assert s == s[..|s|];
  if |s| == 0 || s == "0" {
    assert OStr2Int(s) == 0 by {reveal OStr2Int; assert Str2Int(s) == 0;}
    assert ValidBitString(s[..i+1]) && ValidBitString(s[i+1..]);
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..]) by {reveal OStr2Int;}
  } else if s == "1" {
    assert OStr2Int(s) == 1 by {reveal OStr2Int; assert Str2Int(s) == 1;}
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..]) by {reveal OStr2Int; reveal Exp_int;}
  } else if i == |s|-1 {
    // s[..i+1] == s and s[i+1..|s|] == ""
    assert OStr2Int(s) == OStr2Int(s[..|s|]);
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..]) by {reveal OStr2Int; reveal Exp_int;}
  } else {
    assert i < |s|-1;

    // Inductive step: apply lemma to the prefix s[..|s|-1]
    var prefix: string := s[..|s|-1];
    assert ValidBitString(prefix);
    Str2IntLemmaAux(prefix, i);

    // The induction hypothesis ensures:
    // OStr2Int(prefix) == OStr2Int(s[..i+1]) * Exp_int(2, (|s|-1-1) - i) + OStr2Int(s[i+1..|s|-1])
    assert prefix == prefix[..|s|-1];
    assert ValidBitString(prefix[i+1..|s|-1]);
    assert OStr2Int(prefix[..|s|-1]) == OStr2Int(prefix[..i+1]) * Exp_int(2, (|s|-1-1) - i) + OStr2Int(prefix[i+1..|s|-1]); // justified by lemma postcondition

    // By definition: OStr2Int(s) = 2 * OStr2Int(prefix) + char2int(s[|s|-1])
    assert prefix + s[|s|-1..|s|] == s[..|s|];
    assert OStr2Int(s) == 2 * OStr2Int(prefix) + char2int(s[|s|-1]) by {reveal OStr2Int;}
    assert OStr2Int(s) == 2 * (OStr2Int(prefix[..i+1]) * Exp_int(2, (|s|-1-1) - i) + OStr2Int(prefix[i+1..|s|-1])) + char2int(s[|s|-1]);
    assert s[..i+1] == prefix[..i+1] && s[i+1..|s|-1] == prefix[i+1..|s|-1];
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + 2 * OStr2Int(s[i+1..|s|-1]) + char2int(s[|s|-1]) by {reveal Exp_int;}

    // By definition: OStr2Int(s[i+1..|s|]) = 2 * OStr2Int(s[i+1..|s|-1]) + char2int(s[|s|-1])
    assert |s[i+1..|s|]| > 0;
    assert s[i+1..|s|] == s[i+1..|s|-1] + s[|s|-1..|s|];
    assert OStr2Int(s[i+1..|s|]) == 2 * OStr2Int(s[i+1..|s|-1]) + char2int(s[|s|-1]) by {reveal OStr2Int;}
    assert OStr2Int(s) == OStr2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + OStr2Int(s[i+1..|s|]);
  }
}

lemma Str2IntLemma(s: string, i: nat)
  requires ValidBitString(s)
  // requires n == |s| - 1
  requires 0 <= i <= |s|-1
  ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  Str2IntLemmaAux(s, i);
  reveal OStr2Int;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  if n == 0 {
    assert Str2Int("")==0; s :="";
  }
  else {
    var st := Zeros(n - 1);
    assert ValidBitString(st);
    assert Str2Int(st) == 0;
    assert |st| == n - 1;
    s := "0" + st;
    assert ValidBitString(s);
    assert s[0] == '0';
    assert s[1..|s|] == st;
    Str2IntLemma(s, 0);
    assert Str2Int(s) == Str2Int("0") * Exp_int(2, |s| - 1) + Str2Int(st);
    assert Str2Int(s) == 0 * Exp_int(2, |s| - 1) + Str2Int(st);
    assert Str2Int(s) == Str2Int(st);
    assert Str2Int(s) == 0;
    assert AllZero(s);
  }
}

predicate AllZero(s: string)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}
