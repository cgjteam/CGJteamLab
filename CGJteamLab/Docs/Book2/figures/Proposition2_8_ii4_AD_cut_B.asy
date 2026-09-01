// Euclid II.8 - the II.4 normal form on A-B-D.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(12.5cm,0);

defaultpen(fontsize(10pt));
pen mainpen = black + linewidth(0.9);
pen cutpen = black + linewidth(0.75);
pen fillA = gray(0.95);
pen fillB = gray(0.90);

// AD is the whole side, cut at B.  AB=3.6, BD=1.8.
real a=3.6;
real b=1.8;
real s=a+b;
pair O=(0,0);
pair A=(0,s), B=(a,s), D=(s,s);
pair E=(0,0), F=(s,0);

// Four actual subregions of the square on AD.
filldraw((0,b)--(a,b)--(a,s)--(0,s)--cycle, fillA, mainpen);       // W
filldraw((a,b)--(s,b)--(s,s)--(a,s)--cycle, fillB, mainpen);       // R
filldraw((0,0)--(a,0)--(a,b)--(0,b)--cycle, fillB, mainpen);       // R
filldraw((a,0)--(s,0)--(s,b)--(a,b)--cycle, fillA, mainpen);       // S_BD

// Emphasize the cuts through B.
draw(B--(a,0), cutpen);
draw((0,b)--(s,b), cutpen);

// Top-side points.
dot(A); dot(B); dot(D);
label("$A$",A,NW);
label("$B$",B,N);
label("$D$",D,NE);

// Region labels.
label("$W=\mathrm{Sq}(BA)$", (a/2,(b+s)/2));
label("$R$", ((a+s)/2,(b+s)/2));
label("$R$", (a/2,b/2));
label("$S_{BD}$", ((a+s)/2,b/2));

label("II.4 on $A-B-D$", (s/2,s+0.7));
label("$S_{AD}\simeq_{\rm sc}(R+W)+(R+S_{BD})$", (s/2,-0.65), S);
