import graph;

size(12cm,0);

pair A = (0.0,4.5);
pair B = (-2.8,0.0);
pair C = (1.2,0.0);
pair D = (4.2,0.0);

/*
  M lies on AC.
*/
pair M = interp(A,C,0.55);

/*
  E lies on the line BM and CE is parallel to AB.
*/
pair vAB = B-A;
pair E = extension(B,M,C,C+vAB);

/*
  R is the intersection of ray CE with AD.
*/
pair R = extension(C,E,A,D);

/*
  X extends AB beyond B.
*/
pair X = B + 0.55*(B-A);

/*
  F extends EC beyond C: E-C-F.
*/
pair F = C + 0.65*(C-E);

/* Main triangle and extension BC-D. */
draw(A--B--C--A, linewidth(0.9));
draw(B--D, linewidth(0.9));

/* Auxiliary construction B-M-E. */
draw(B--E, dashed);

/* Parallel through C and its extension. */
draw(F--E, dashed);

/* Segment AD containing R. */
draw(A--D, dashed);

/* Extension of AB used for I.29. */
draw(A--X, dashed);

/* Points. */
dot(A);
dot(B);
dot(C);
dot(D);
dot(M);
dot(E);
dot(R);
dot(X);
dot(F);

/* Labels. */
label("$A$", A, N);
label("$B$", B, SW);
label("$C$", C, S);
label("$D$", D, SE);

label("$M$", M, NW);
label("$E$", E, NE);
label("$R$", R, NE);
label("$X$", X, SW);
label("$F$", F, SE);

/*
  Parallel marks on AB and CE.
*/
pair p1 = interp(A,B,0.68);
pair p2 = interp(C,E,0.48);

pair u1 = unit(B-A);
pair n1 = (-u1.y,u1.x);

pair u2 = unit(E-C);
pair n2 = (-u2.y,u2.x);

draw(p1 - 0.13*u1 + 0.12*n1 -- p1 -- p1 + 0.13*u1 + 0.12*n1);
draw(p2 - 0.13*u2 + 0.12*n2 -- p2 -- p2 + 0.13*u2 + 0.12*n2);

/*
  Configuration annotations.
*/
label("$A-M-C$", (-1.1,3.75), W);
label("$B-M-E$", (-2.1,2.55), W);

label("$AB\parallel CE$", (1.1,3.5), E);

label("$A-R-D$", (3.3,2.1), E);
label("$E-C-F$", (1.7,-1.15), E);
