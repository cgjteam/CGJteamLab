import graph;
settings.outformat = "pdf";
size(470,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = black+0.9bp;
pen auxpen = black+0.65bp;
pen lightpen = gray(0.62)+0.55bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

// The formal I.20 comparison used to prove AF < AB.
// E-A-F-T are collinear, AT is copied from AB, and EF is copied from EB.
pair A=(0,0), E=(0,3.2), B=(4.4,0);
pair F=(0,-1.55), T=(0,-4.35);

draw(E--T, mainpen);
draw(A--B, mainpen);
draw(E--B, auxpen);
draw(T--B, lightpen);

// Congruence marks: AT ~= AB.
draw((-0.13,-2.15)--(0.13,-2.15), auxpen);
draw((2.15,-0.13)--(2.15,0.13), auxpen);

// Congruence marks: EF ~= EB.
pair mEF=(E+F)/2;
draw(mEF+(-0.12,-0.08)--mEF+(0.12,0.08), auxpen);
draw(mEF+(-0.12,0.08)--mEF+(0.12,-0.08), auxpen);
pair mEB=(E+B)/2;
pair d=unit(B-E); pair n=(-d.y,d.x);
draw(mEB-0.14*n--mEB+0.14*n, auxpen);
draw(mEB+0.19*d-0.14*n--mEB+0.19*d+0.14*n, auxpen);

dotlabel("E",E,NW);
dotlabel("A",A,W);
dotlabel("F",F,W);
dotlabel("T",T,SW);
dotlabel("B",B,E);

label("$E-A-F-T$", (-0.60,-0.65), W);
label("$AT\cong AB$", (2.2,-3.65));
label("$EF\cong EB$", (2.45,1.65));
