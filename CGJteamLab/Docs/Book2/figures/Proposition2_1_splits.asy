import graph;

size(470,0);
defaultpen(fontsize(9pt));

pen main=black+0.85bp;
pen cut=black+1.15bp;
pen aux=black+0.55bp+dashed;

void pointmark(pair P) {
  dot(P, black+2.0bp);
}

// Panel (a): binary split.
pair s1=(0,0);
pair B=(0,0)+s1;
pair C=(6,0)+s1;
pair E=(6,3)+s1;
pair D=(0,3)+s1;
pair M=(2.4,0)+s1;
pair L=(2.4,3)+s1;
pair X=(2.4,1.8)+s1;

draw(B--C--E--D--cycle,main);
draw(M--L,cut);
draw(D--C,aux);
pointmark(X);

label("$B$",B,SW);
label("$M$",M,S);
label("$C$",C,SE);
label("$D$",D,NW);
label("$L$",L,N);
label("$E$",E,NE);
label("$X$",X,E);
label("$BMLD$",(1.15,0.38)+s1);
label("$MCEL$",(4.20,0.38)+s1);
label("(a) binary split",(3,-0.72)+s1,S);

// Panel (b): three-part split.
pair s2=(9.0,0);
pair B2=(0,0)+s2;
pair C2=(7,0)+s2;
pair E2=(7,3)+s2;
pair D2=(0,3)+s2;
pair M2=(2,0)+s2;
pair L2=(2,3)+s2;
pair N2=(4.5,0)+s2;
pair K2=(4.5,3)+s2;
pair X2=(2,3-(3.0/7.0)*2)+s2;
// Y is the intersection of L-C with N-K.
pair Y2=(4.5,3-(3.0/5.0)*(4.5-2))+s2;

draw(B2--C2--E2--D2--cycle,main);
draw(M2--L2,cut);
draw(N2--K2,cut);
draw(D2--C2,aux);
draw(L2--C2,aux);
pointmark(X2);
pointmark(Y2);

label("$B$",B2,SW);
label("$M$",M2,S);
label("$N$",N2,S);
label("$C$",C2,SE);
label("$D$",D2,NW);
label("$L$",L2,N);
label("$K$",K2,N);
label("$E$",E2,NE);
label("$X$",X2,SW);
label("$Y$",Y2,NE);
label("$BMLD$",(0.9,0.34)+s2);
label("$MNKL$",(3.25,0.34)+s2);
label("$NCEK$",(5.75,2.18)+s2);
label("(b) three-part split",(3.5,-0.72)+s2,S);
