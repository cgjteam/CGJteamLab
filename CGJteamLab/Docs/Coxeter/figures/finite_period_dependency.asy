// finite_period_dependency.asy
// Logical architecture of the general finite Coxeter-period result.

import CoxeterFiguresCommon;

size(14cm);

void node(string s, pair C, real w=4.9, real h=0.90) {
  draw(box(C+(-w/2,-h/2), C+(w/2,h/2)), mainpen);
  label(s, C);
}

pair A = (0,6.0);
pair B = (0,4.0);
pair C = (0,2.0);
pair D = (0,0.0);
pair E = (6.8,6.0);
pair F = (-6.8,0.0);

node("\shortstack{oriented radial\\$p$-polygon}", A);
node("\shortstack{carrier transport\\chain}", B);
node("\shortstack{first carrier return\\at $p$}", C);
node("\shortstack{\texttt{ReflectionPair}\\\texttt{ExactPeriod} $p$}", D, 5.2);
node("\shortstack{existence principle\\for all $p\ge3$}", E, 5.3);
node("\shortstack{Hilbert right angle\\special case $p=2$}", F, 5.1);

draw(A+(0,-0.45)--B+(0,0.45), mainpen, Arrow);
draw(B+(0,-0.45)--C+(0,0.45), mainpen, Arrow);
draw(C+(0,-0.45)--D+(0,0.45), mainpen, Arrow);

draw(E+(-2.65,0)--A+(2.45,0), mainpen, Arrow);
draw(F+(2.55,0)--D+(-2.60,0), mainpen, Arrow);
