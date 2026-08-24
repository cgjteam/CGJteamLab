import graph;
import math;

size(520,0);
defaultpen(fontsize(8.5pt));

pen mainpen = black+0.8bp;
pen auxpen = gray(0.45)+0.7bp;
pen lightpen = gray(0.72)+0.6bp;
pen fillpen = gray(0.92);

void pt(pair P, string s, pair d=(0,0.16)) {
  dot(P, mainpen);
  label("$"+s+"$", P+d);
}

void paneltitle(string s, pair P) {
  label("\textbf{"+s+"}", P, S);
}

// ------------------------------------------------------------------
// Panel (a): final classical configuration.
// ------------------------------------------------------------------
pair O1=(0,0);
pair B1=O1+(-2.8,0);
pair E1=O1+(0,0);
pair C1=O1+(2.8,0);
pair F1=O1+(-0.8,2.2);
pair G1=O1+(2.0,2.2);
pair A1=O1+(0.9,2.2);

filldraw(F1--E1--C1--G1--cycle, fillpen, mainpen);
draw(B1--C1, mainpen);
draw(A1--B1, mainpen);
draw(A1--C1, mainpen);
draw(A1--E1, auxpen);
draw(F1--G1, mainpen);

pt(A1,"A",(0,0.18));
pt(B1,"B",(0,-0.20));
pt(E1,"E",(0,-0.20));
pt(C1,"C",(0,-0.20));
pt(F1,"F",(-0.12,0.18));
pt(G1,"G",(0.12,0.18));

// midpoint ticks on BE and EC
pair t1=(-1.35,0); pair t2=(1.35,0);
draw(t1+(-0.05,-0.10)--t1+(0.05,0.10), mainpen);
draw(t2+(-0.05,-0.10)--t2+(0.05,0.10), mainpen);

// angle marker at E between EC and EF
real a1=degrees(atan2(F1.y-E1.y,F1.x-E1.x));
draw(arc(E1,0.45,0,a1), mainpen);
label("$\angle FEC$", E1+(0.15,0.62), E);

paneltitle("(a) final configuration", O1+(0,3.35));

// ------------------------------------------------------------------
// Panel (b): remote-triangle reduction used for the midpoint halves.
// ------------------------------------------------------------------
pair O2=(8.0,0);
pair B2=O2+(-2.8,0);
pair E2=O2+(-1.4,0);
pair C2=O2+(0,0);
pair U2=O2+(1.4,0);
pair V2=O2+(2.8,0);
pair A2=O2+(-1.0,2.2);
pair D2=O2+(1.8,2.2);

draw(B2--V2, mainpen);
draw(A2--D2, auxpen);
draw(A2--B2, mainpen);
draw(A2--E2, mainpen);
draw(A2--C2, mainpen);
draw(D2--U2, mainpen);
draw(D2--V2, mainpen);

pt(A2,"A",(0,0.18));
pt(D2,"D",(0,0.18));
pt(B2,"B",(0,-0.20));
pt(E2,"E",(0,-0.20));
pt(C2,"C",(0,-0.20));
pt(U2,"U",(0,-0.20));
pt(V2,"V",(0,-0.20));

// equal-base ticks BE, EC, UV
for(pair t : new pair[] {O2+(-2.1,0), O2+(-0.7,0), O2+(2.1,0)}) {
  draw(t+(-0.05,-0.10)--t+(0.05,0.10), mainpen);
}
label("$AD \parallel BC$", O2+(0.4,2.42));
label("I.38", O2+(1.9,1.1));
paneltitle("(b) common remote comparison", O2+(0,3.35));

// ------------------------------------------------------------------
// Panel (c): angle ray meets the upper parallel.
// ------------------------------------------------------------------
pair O3=(16.0,0);
pair E3=O3+(-1.7,0);
pair C3=O3+(1.2,0);
pair A3=O3+(0.4,2.1);
pair Q3=O3+(2.6,2.1);
pair F3=O3+(-0.35,2.1);
pair R3=E3+1.24*(F3-E3);

draw(E3--C3, mainpen);
draw(A3--Q3, mainpen);
draw(E3--R3, mainpen);
draw(E3+(-0.7,0)--C3+(0.7,0), lightpen);
draw(A3+(-1.5,0)--Q3+(0.4,0), lightpen);

pt(E3,"E",(0,-0.20));
pt(C3,"C",(0,-0.20));
pt(F3,"F",(-0.10,0.18));
pt(A3,"A",(0,0.18));
pt(Q3,"Q",(0,0.18));
pt(R3,"R",(0.10,0.18));

label("$AQ \parallel EC$", O3+(0.9,2.43));
label("$F=A$ is allowed", O3+(0.55,1.15));
paneltitle("(c) oriented intersection", O3+(0,3.35));

// separators
path s1=(4.0,-0.55)--(4.0,3.55);
path s2=(12.0,-0.55)--(12.0,3.55);
draw(s1, lightpen);
draw(s2, lightpen);
