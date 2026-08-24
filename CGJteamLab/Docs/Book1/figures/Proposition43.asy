import graph;

size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen = linewidth(0.9);
pen innerpen = linewidth(0.8);
pen diagpen = linewidth(0.65) + dashed;
pen lightpen = gray(0.72) + linewidth(0.45);
pen compfill1 = gray(0.90) + opacity(0.55);
pen compfill2 = gray(0.78) + opacity(0.35);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

// Big parallelogram ABCD.
pair A=(0,3.0);
pair B=(6.0,3.0);
pair D=(1.0,0.0);
pair C=(7.0,0.0);

// All side points use the same affine parameter t, so K lies on AC and
// AGKE, KFCH are genuine parallelograms.
real t=0.45;
pair K=A+t*(C-A);
pair G=A+t*(B-A);
pair E=A+t*(D-A);
pair F=B+t*(C-B);
pair H=D+t*(C-D);

// Shade exactly the two complement regions represented by the Lean terms.
fill(G--B--F--K--cycle, compfill1);
fill(E--K--H--D--cycle, compfill2);

// Outer parallelogram and its main diagonal.
draw(A--B--C--D--cycle, mainpen);
draw(A--C, diagpen);

// The two parallelograms about the diagonal.
draw(G--K, innerpen);
draw(E--K, innerpen);
draw(F--K, innerpen);
draw(H--K, innerpen);

// Diagonals used by the formal triangulations of the two complements.
draw(B--K, diagpen);
draw(D--K, diagpen);

// Point labels.
pt("A",A,NW);
pt("B",B,NE);
pt("C",C,SE);
pt("D",D,SW);
pt("K",K,N);
pt("G",G,N);
pt("E",E,W);
pt("F",F,E);
pt("H",H,S);

// Minimal conceptual annotations.
label("$AGKE$", (1.35,2.72), fontsize(9));
label("$GBFK$", (4.80,2.72), fontsize(9));
label("$EKHD$", (1.60,1.02), fontsize(9));
label("$KFCH$", (5.30,0.34), fontsize(9));
label("triangulation diagonals $BK$, $KD$", (3.55,-0.58), fontsize(9));
