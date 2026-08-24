import graph;

size(13.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(0.9);
pen innerpen = linewidth(0.8);
pen diagpen = linewidth(0.65) + dashed;
pen lightpen = gray(0.70) + linewidth(0.45);
pen oldfill = gray(0.86) + opacity(0.48);
pen newfill = gray(0.68) + opacity(0.30);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

// Affine model of the exact Lean configuration.
pair H=(0,0);
pair u=(6.0,0);
pair v=(1.35,4.0);
pair L=H+u;
pair F=H+v;
pair K=H+u+v;
real t=0.42;

pair A=H+t*u;
pair G=H+t*v;
pair B=H+t*(u+v);
pair M=L+t*v;
pair E=F+t*u;

// The target and original parallelograms are the two I.43 complements.
fill(A--B--M--L--cycle, newfill);
fill(B--E--F--G--cycle, oldfill);

// Big parallelogram and its diameter.
draw(H--L--K--F--cycle, mainpen);
draw(H--K, diagpen);

// Two parallelograms about the diameter.
draw(H--A--B--G--cycle, innerpen);
draw(B--M--K--E--cycle, innerpen);

// Complement boundaries emphasized by the construction.
draw(A--B--M--L--cycle, mainpen);
draw(B--E--F--G--cycle, mainpen);

// Construction carriers.
draw(H--F, lightpen);
draw(L--K, lightpen);
draw(H--L, lightpen);
draw(F--K, lightpen);

pt("H",H,SW);
pt("A",A,S);
pt("L",L,S);
pt("G",G,W);
pt("B",B,SE);
pt("M",M,E);
pt("F",F,NW);
pt("E",E,N);
pt("K",K,NE);

label("$H-A-L$", (3.0,-0.55));
label("$H-G-F$", (0.02,2.25), W);
label("$H-B-K$", (3.95,2.55), NW);
label("$G-B-M$", (3.55,1.35));
label("$F-E-K$", (4.45,4.35));
label("diameter $HK$", (4.05,2.02), NW);

label("target $ABML$", (4.85,0.72));
label("placed $BEFG$", (2.25,3.20));
