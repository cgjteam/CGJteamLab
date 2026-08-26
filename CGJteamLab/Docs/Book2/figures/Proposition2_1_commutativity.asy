import graph;

size(450,0);
defaultpen(fontsize(9pt));

pen main=black+0.9bp;
pen emph=black+1.2bp;
pen guide=black+0.55bp+dashed;

void rightmark(pair V, pair e1, pair e2) {
  pair p1=V+0.34*e1;
  pair p2=p1+0.34*e2;
  pair p3=V+0.34*e2;
  draw(p1--p2--p3,main);
}

// Left: ABCD contained by PQ,RS.
pair s1=(0,0);
pair A=(0,0)+s1;
pair B=(4,0)+s1;
pair C=(4,2.7)+s1;
pair D=(0,2.7)+s1;

draw(A--B--C--D--cycle,main);
draw(A--B,emph);
draw(B--C,emph);
rightmark(B,(-1,0),(0,1));
label("$A$",A,SW);
label("$B$",B,SE);
label("$C$",C,NE);
label("$D$",D,NW);
label("$AB\cong PQ$",(2,-0.36)+s1,S);
label("$BC\cong RS$",(3.62,1.35)+s1,W);
label("$ABCD:\ (PQ,RS)$",(2,3.35)+s1,N);

// Arrow between presentations.
draw((5.25,1.35)--(7.25,1.35),Arrow);
label("cyclic presentation",(6.25,1.63),N);

// Right: the same shape read as BCDA, contained by RS,PQ.
pair s2=(8.2,0);
pair Bp=(0,0)+s2;
pair Cp=(4,0)+s2;
pair Dp=(4,2.7)+s2;
pair Ap=(0,2.7)+s2;

draw(Bp--Cp--Dp--Ap--cycle,main);
draw(Bp--Cp,emph);
draw(Cp--Dp,emph);
rightmark(Cp,(-1,0),(0,1));
label("$B$",Bp,SW);
label("$C$",Cp,SE);
label("$D$",Dp,NE);
label("$A$",Ap,NW);
label("$BC\cong RS$",(2,-0.36)+s2,S);
label("$CD\cong PQ$",(3.62,1.35)+s2,W);
label("$BCDA:\ (RS,PQ)$",(2,3.35)+s2,N);

label("same rectangle term up to cyclic normalization",(6.10,-0.95),S);
