import graph;
settings.outformat = "pdf";
size(660,0);
defaultpen(fontsize(8.7pt)+black);

pen mainpen = black+0.85bp;
pen cutpen = black+1.05bp;
pen lightpen = gray(0.58)+0.55bp;
pen commonfill = gray(0.90);

// Two dissection pictures for the second Common-Notion-3 step.
// Left: Rect(DF,AF) = Rect(DA,AF) + Sq(AF).
// Right: Sq(AB) = Rect(AB,AH) + Rect(AB,HB).

// Left panel.
pair O=(0,0);
real h=3.0;
real da=4.0;
real af=2.0;
pair D=O+(0,h), A=O+(da,h), F=O+(da+af,h);
pair D0=O+(0,0), A0=O+(da,0), F0=O+(da+af,0);

fill(D--A--A0--D0--cycle, commonfill);
draw(D--F--F0--D0--cycle, mainpen);
draw(A--A0, cutpen);

label("$\mathrm{Rect}(DA,AF)$", (D+A+A0+D0)/4);
label("$\mathrm{Sq}(AF)$", (A+F+F0+A0)/4);
label("II.3", O+(3.0,3.75), N);
label("$D$",D,NW); label("$A$",A,N); label("$F$",F,NE);

// Right panel.
pair sh=(9.0,0);
real ab=6.0;
real ah=4.0;
pair A2=sh+(0,3), H2=sh+(ah,3), B2=sh+(ab,3);
pair A2d=sh+(0,0), H2d=sh+(ah,0), B2d=sh+(ab,0);

fill(A2--H2--H2d--A2d--cycle, commonfill);
draw(A2--B2--B2d--A2d--cycle, mainpen);
draw(H2--H2d, cutpen);

label("$\mathrm{Rect}(AB,AH)$", (A2+H2+H2d+A2d)/4);
label("$\mathrm{Rect}(AB,HB)$", (H2+B2+B2d+H2d)/4);
label("II.2", sh+(3.0,3.75), N);
label("$A$",A2,NW); label("$H$",H2,N); label("$B$",B2,NE);

// The shaded left regions are the common rectangles after side transport.
label("common rectangle after $DA\cong AB$, $AF\cong AH$", (7.4,-0.75), S);
