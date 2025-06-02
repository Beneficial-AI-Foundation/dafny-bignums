lemma Bounding(x:int, d:int, n: int)
  requires x == d * n
  requires x > -d
  requires x < d
  ensures x == 0
{}
