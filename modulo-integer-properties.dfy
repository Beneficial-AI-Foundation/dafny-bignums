include "bound.dfy"

lemma ModuloDistributivityAdd_int(a: int, b: int, z: int)
  requires z > 0
  ensures (a + b) % z == ((a % z) + (b % z)) % z
{
  // Expand a and b using quotient and remainder
  var qa := a / z;
  var ra := a % z;
  var qb := b / z;
  var rb := b % z;

  assert a == qa * z + ra;
  assert b == qb * z + rb;

  assert a + b == (qa * z + ra) + (qb * z + rb);
  assert a + b == (qa + qb) * z + (ra + rb);

  assert (a + b) % z == (ra + rb) % z by {IgnoreMod(qa+qb, ra+rb, a+b, z);}

  assert ((a % z) + (b % z)) % z == (ra + rb) % z;
}

lemma IgnoreMod(a: int, b:nat, c:int, z:nat)
  requires a * z + b == c
  requires z > 0
  ensures b % z == c % z
  ensures (a * z) % z == 0
{
  assert c - a*z == (b/z)*z + (b % z);
  assert (c/z)*z + (c % z) - a*z == (b/z)*z + (b % z);
  assert (c/z - a)*z + (c % z) == (b/z)*z + (b % z);
  assert (c/z - a - b/z)*z  == b % z - c % z;
  Bounding(b % z - c % z, z, c/z - a - b/z);
}

lemma IgnoreMod'(a :int, z:nat)
  requires z > 0
  ensures (a * z) % z == 0
{
  IgnoreMod(a, 0, a*z, z);
}

lemma ModuloDistributivityMul_int(x: int, y: int, z: int)
  requires z > 0
  ensures (x * y) % z == ((x % z) * (y % z)) % z
{

  var qx := x / z;
  var rx := x % z;
  var qy := y / z;
  var ry := y % z;

  assert x == qx * z + rx;
  assert y == qy * z + ry;

  assert x * y == (qx*z + rx)*(qy*z + ry);
  assert x * y == qx*qy*z*z + qx*ry*z + qy*rx*z + rx*ry;
  calc {
    (qx*qy*z*z + qx*ry*z + qy*rx*z) % z;
  ==
    (qx*qy*z + qx*ry + qy*rx)*z % z;
  ==
    {IgnoreMod'(qx*qy*z + qx*ry + qy*rx, z);}
    0;
  }
  calc {
    x * y % z;
  ==
    (qx*qy*z*z + qx*ry*z + qy*rx*z + rx*ry ) % z;
  ==
    {
      ModuloDistributivityAdd_int(qx*qy*z*z + qx*ry*z + qy*rx*z, rx*ry, z);
    }
    ((qx*qy*z*z + qx*ry*z + qy*rx*z) % z + rx*ry % z) % z;
  ==
    (rx*ry % z) % z;
  ==
    rx*ry % z;
  }
  assert (x * y) % z == (rx * ry) % z;

  assert ((x % z) * (y % z)) % z == (rx * ry) % z;
}
