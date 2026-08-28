// CoxeterFiguresCommon.asy
// Shared black-and-white style for the Coxeter supplement.

size(9cm);

defaultpen(fontsize(10pt));

pen mainpen = linewidth(1.0);
pen axispen = linewidth(1.2);
pen helppen = dashed + linewidth(0.7);

pair midpoint(pair P, pair Q) {
  return (P + Q)/2;
}

path lineThrough(pair P, pair Q, real back=0.25, real front=0.25) {
  pair v = Q - P;
  return P - back*v -- Q + front*v;
}

void markPoint(pair P) {
  dot(P);
}

void markPointLabel(string s, pair P, align a=NE) {
  dot(P);
  label(s, P, a);
}
