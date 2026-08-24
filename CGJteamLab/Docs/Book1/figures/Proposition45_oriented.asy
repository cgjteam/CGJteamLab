import graph;

size(13.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(0.9);
pen oldpen = linewidth(1.0);
pen newpen = linewidth(1.0);
pen lightpen = gray(0.65) + linewidth(0.55);
pen raypen = gray(0.50) + linewidth(0.65) + dashed;
pen oldfill = gray(0.90) + opacity(0.45);
pen newfill = gray(0.72) + opacity(0.28);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

// Exact affine model of the oriented-placement configuration.
pair T=(0,0);
pair U=(3,0);
pair V=(3.8,2.0);
pair S=(0.8,2.0);
pair E=(4.6,0);
pair G=(3.64,1.6);
pair F=E+G-U;

fill(S--T--U--V--cycle, oldfill);
fill(U--E--F--G--cycle, newfill);

draw(S--T--U--V--cycle, oldpen);
draw(U--E--F--G--cycle, newpen);

// Produced carrier T-U-E and ray U-V-G.
draw(T--E, lightpen);
draw(U--V, raypen);

pt("S",S,NW);
pt("T",T,SW);
pt("U",U,S);
pt("V",V,NW);
pt("E",E,SE);
pt("F",F,NE);
pt("G",G,W);

label("$T-U-E$", (2.30,-0.45));
label("$G$ on ray $UV$", (4.30,1.15), E);
label("old $STUV$", (1.35,1.25));
label("placed $UEFG$", (4.55,0.75));
