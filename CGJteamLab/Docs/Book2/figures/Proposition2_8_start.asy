// Euclid II.8 - starting produced-segment configuration.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);

defaultpen(fontsize(10pt));
pen mainpen = black + linewidth(0.9);
pen auxpen = black + linewidth(0.6);

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void tick(pair A, pair B, int n=1) {
  pair M=(A+B)/2;
  pair v=unit(B-A);
  pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.13;
    draw(M+d*v-0.11*w--M+d*v+0.11*w, mainpen);
  }
}

// Baseline order A-C-B-D with BD congruent to BC.
pair A=(0,4.8), C=(2.0,4.8), B=(4.0,4.8), D=(6.0,4.8);
pair E=(0,0), F=(6.0,0);

// Square on AD and the produced baseline.
draw(A--D--F--E--cycle, mainpen);
draw(A--C--B--D, mainpen);

// Congruence marks on CB and BD.
tick(C,B,2);
tick(B,D,2);

// Points and labels.
dotlabel("A",A,NW);
dotlabel("C",C,N);
dotlabel("B",B,N);
dotlabel("D",D,NE);
dotlabel("E",E,SW);
dotlabel("F",F,SE);

label("$A-C-B-D$", (3.0,5.55));
label("$BD\cong BC$", (4.0,4.25), S);
label("square on $AD$", (3.0,2.25));
