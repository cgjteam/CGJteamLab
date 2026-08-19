import graph;

size(500,0);
defaultpen(fontsize(9pt));

void dotlabel(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

void panel(pair O, string title, real ax, real dx, real ex, real fx, bool showG=false) {
  pair B=O+(0,0);
  pair C=O+(2,0);
  pair A=O+(ax,2);
  pair D=O+(dx,2);
  pair E=O+(ex,2);
  pair F=O+(fx,2);

  filldraw(A--B--C--D--cycle, lightgray+opacity(0.22), black+0.8pt);
  filldraw(E--B--C--F--cycle, gray+opacity(0.12), black+0.8pt);
  draw(A--F, black+0.5pt);
  draw(B--C, black+0.5pt);

  dotlabel("A",A,NW);
  dotlabel("B",B,SW);
  dotlabel("C",C,SE);
  if (abs(ex-dx) > 0.001) {
    dotlabel("D",D,N);
    dotlabel("E",E,N);
  } else {
    dot(D);
    label("$D=E$",D,N);
  }
  dotlabel("F",F,NE);

  if(showG) {
    pair G=intersectionpoint(E--B,D--C);
    draw(E--B, black+0.7pt);
    draw(D--C, black+0.7pt);
    dotlabel("G",G,E);
  }
  label(title, O+(1,2.65));
}

panel((0,0), "(a) overlap: $A,E,D,F$", -1,1,0,2,false);
panel((5.2,0), "(b) common endpoint", -1,1,1,3,false);
panel((11.0,0), "(c) disjoint: $A,D,E,F$", -1,1,1.6,3.6,true);
