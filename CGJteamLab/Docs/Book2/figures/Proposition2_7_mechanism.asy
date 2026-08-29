import graph;
size(430,0);
defaultpen(fontsize(9pt)+black);

// Euclid II.7 as used by the current Lean proof.
// Choose AC=5 and CB=3 only to make the decomposition visible.
// These coordinates are diagrammatic, not numerical proof data.

real a=5;
real b=3;
real w=a+b;

// Left panel: square W on AB, cut at C.
// Coordinates are shifted left.
pair O=(-10,0);
pair A=O+(0,0), C=O+(a,0), B=O+(w,0);
pair D=O+(0,w), E=O+(w,w);
pair P=O+(a,w), Q=O+(a,a), R=O+(w,a);

// Light grayscale fills distinguish the four exact pieces.
fill(A--C--Q--(O+(0,a))--cycle, gray(0.94)); // S
fill(C--B--R--Q--cycle, gray(0.88));         // X
fill((O+(0,a))--Q--P--D--cycle, gray(0.88)); // X
fill(Q--R--E--P--cycle, gray(0.97));         // T

draw(A--B--E--D--cycle, linewidth(0.8));
draw(C--P, linewidth(0.65));
draw(O+(0,a)--R, linewidth(0.65));

dot(A); dot(C); dot(B);
label("$A$",A,S); label("$C$",C,S); label("$B$",B,S);
label("$W=\mathrm{Sq}(AB)$", (D+E)/2, N);
label("$S$", O+(2.5,2.5));
label("$X$", O+(6.5,2.5));
label("$X$", O+(2.5,6.5));
label("$T$", O+(6.5,6.5));
label("$W=(X+S)+(X+T)$", O+(4, -1.15));

// Right panel: R = Rect(AB,AC), split as S + X.
pair O2=(2,1.5);
pair A2=O2+(0,0), C2=O2+(a,0), B2=O2+(w,0);
pair D2=O2+(0,a), E2=O2+(w,a), P2=O2+(a,a);

fill(A2--C2--P2--D2--cycle, gray(0.94)); // S
fill(C2--B2--E2--P2--cycle, gray(0.88)); // X

draw(A2--B2--E2--D2--cycle, linewidth(0.8));
draw(C2--P2, linewidth(0.65));

dot(A2); dot(C2); dot(B2);
label("$A$",A2,S); label("$C$",C2,S); label("$B$",B2,S);
label("$R=\mathrm{Rect}(AB,AC)$", (D2+E2)/2, N);
label("$S$", O2+(2.5,2.5));
label("$X$", O2+(6.5,2.5));
label("$R=X+S$", O2+(4,-1.15));
