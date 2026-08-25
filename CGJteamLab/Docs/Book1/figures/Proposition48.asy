import graph;

size(470,0);
defaultpen(fontsize(9pt));

pen main=black+0.85bp;
pen aux=black+0.55bp+dashed;
pen emph=black+1.15bp;

void onetick(pair P, pair Q) {
  pair v=unit(Q-P);
  pair n=(-v.y,v.x);
  pair M=(P+Q)/2;
  draw(M-0.10*n--M+0.10*n,main);
}

// Panel (a): Euclid's comparison triangle.
pair s1=(0,0);
pair A=(0,0)+s1;
pair C=(0,4)+s1;
pair B=(3,1.2)+s1;
real r=sqrt(3^2+1.2^2);
pair D=(-r,0)+s1;

draw(A--B--C--cycle,main);
draw(D--A--C--cycle,main);
draw(D--C,aux);

// Right-angle mark for DAC.
pair q1=A+(-0.34,0);
pair q2=A+(-0.34,0.34);
pair q3=A+(0,0.34);
draw(q1--q2--q3,main);

onetick(A,B);
onetick(A,D);

label("$A$",A,S);
label("$B$",B,SE);
label("$C$",C,N);
label("$D$",D,SW);
label("$AD=AB$",(-0.05,-0.55)+s1,S);
label("(a)",(0,-1.15)+s1,S);

// Panel (b): strict inner-square decomposition used by the formal proof.
pair s2=(10.2,0.1);
pair Ap=(0,0)+s2;
pair Bp=(4,0)+s2;
pair Cp=(4,4)+s2;
pair Dp=(0,4)+s2;
pair X=(2.35,0)+s2;
pair Y=(0,2.35)+s2;
pair Z=(2.35,2.35)+s2;

draw(Ap--Bp--Cp--Dp--cycle,main);
draw(Ap--X--Z--Y--cycle,emph);
draw(Dp--Bp,aux);
draw(Y--X,emph);

label("$A'$",Ap,SW);
label("$B'$",Bp,SE);
label("$C'$",Cp,NE);
label("$D'$",Dp,NW);
label("$X$",X,S);
label("$Y$",Y,W);
label("$Z$",Z,NE);

label("$Y D' X$",(0.65,3.05)+s2,NW);
label("$X B' D'$",(3.18,1.72)+s2,E);
label("inner square",(1.15,1.05)+s2);
label("(b)",(2,-1.05)+s2,S);
