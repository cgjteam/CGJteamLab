// Proposition2_7_rectangle_swap_II3.asy
// The geometric reorientation needed before applying II.3 in Proposition II.7.
// ASCII-only source.

settings.outformat = "pdf";
size(14.2cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = black+0.85bp;
pen cutpen = black+0.65bp;
pen arrowpen = gray(0.45)+0.7bp;
pen fillX = gray(0.88);
pen fillS = gray(0.95);

// Panel 1: one concrete cross rectangle X with ordered sides AC, CB.
pair O1=(0,0);
real ac=2.7, cb=1.8;
pair T0=O1, T1=O1+(ac,0), T2=O1+(ac,cb), T3=O1+(0,cb);
filldraw(T0--T1--T2--T3--cycle, fillX, mainpen);
label("$T_0$",T0,SW); label("$T_1$",T1,SE);
label("$T_2$",T2,NE); label("$T_3$",T3,NW);
label("$AC$",(T0+T1)/2,S);
label("$CB$",(T1+T2)/2,E);
label("$X$",(T0+T2)/2);
label("original contained-by presentation",O1+(ac/2,cb+0.62),N);

// Arrow: cyclic presentation T0T1T2T3 -> T1T2T3T0.
draw(O1+(3.25,0.9)--O1+(4.65,0.9), arrowpen, Arrow);
label("cyclic swap", O1+(3.95,1.12), N);

// Panel 2: same rectangle, reread with the two side magnitudes exchanged.
pair O2=(5.0,0);
pair U0=O2, U1=O2+(cb,0), U2=O2+(cb,ac), U3=O2+(0,ac);
filldraw(U0--U1--U2--U3--cycle, fillX, mainpen);
label("$T_1$",U0,SW); label("$T_2$",U1,SE);
label("$T_3$",U2,NE); label("$T_0$",U3,NW);
label("$CB$",(U0+U1)/2,S);
label("$AC$",(U1+U2)/2,E);
label("$X_{\rm rot}$",(U0+U2)/2);
label("presentation required by II.3",O2+(cb/2,ac+0.62),N);

// Arrow to the actual II.3 split on the reversed baseline B-C-A.
draw(O2+(2.25,1.35)--O2+(3.75,1.35), arrowpen, Arrow);
label("II.3", O2+(3.0,1.58), N);

// Panel 3: R = Rect(BA,CA) split at C into X_rot + S.
pair O3=(9.2,0);
real h=2.7;
real left=1.8, right=2.7;
pair B=O3, C=O3+(left,0), A=O3+(left+right,0);
pair Bp=B+(0,h), Cp=C+(0,h), Ap=A+(0,h);
fill(B--C--Cp--Bp--cycle, fillX);
fill(C--A--Ap--Cp--cycle, fillS);
draw(B--A--Ap--Bp--cycle, mainpen);
draw(C--Cp, cutpen);
for(pair P : new pair[] {B,C,A}) dot(P,black);
label("$B$",B,S); label("$C$",C,S); label("$A$",A,S);
label("$X_{\rm rot}$",(B+Cp)/2);
label("$S$",(C+Ap)/2);
label("$R=\mathrm{Rect}(BA,CA)$",(Bp+Ap)/2,N);
label("$R\sim_{\rm sc}X_{\rm rot}+S$",O3+((left+right)/2,-0.62),S);
