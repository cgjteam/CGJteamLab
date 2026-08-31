import graph;
size(660,0);

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.62)+0.45bp;
pen fillpen=gray(0.92);

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}
void tick(pair A, pair B, int n=1) {
  pair M=(A+B)/2;
  pair v=unit(B-A);
  pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.11;
    draw(M+d*v-0.09*w--M+d*v+0.09*w, mainpen);
  }
}

// Panel (a): produced segment and square on AD.
pair O1=(0,0);
pair A=O1+(0,0), C=O1+(1.5,0), B=O1+(3.0,0), D=O1+(4.5,0);
pair E=O1+(0,4.5), F=O1+(4.5,4.5);
filldraw(A--D--F--E--cycle, fillpen, mainpen);
draw(A--C--B--D, mainpen);
tick(C,B,2); tick(B,D,2);
dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("B",B,S); dotlabel("D",D,SE);
dotlabel("E",E,NW); dotlabel("F",F,NE);
label("$BD=BC$", O1+(2.25,-0.55));
label("(a) produced $D$ and square on $AD$", O1+(2.25,5.05));

// Panel (b): II.4 normal form.  R is repeated, W = Sq(BA), S = Sq(BD).
pair O2=(6.0,0);
real s=4.5, cut=3.0;
pair p00=O2, p10=O2+(s,0), p11=O2+(s,s), p01=O2+(0,s);
filldraw(p00--p10--p11--p01--cycle, fillpen, mainpen);
draw(O2+(cut,0)--O2+(cut,s), auxpen);
draw(O2+(0,cut)--O2+(s,cut), auxpen);
label("$W$", O2+(1.5,1.5));
label("$R$", O2+(3.75,1.5));
label("$R$", O2+(1.5,3.75));
label("$S_{BD}$", O2+(3.75,3.75));
label("(b) II.4 on $A-B-D$", O2+(2.25,5.05));
label("$S_{AD}=(R+W)+(R+S_{BD})$", O2+(2.25,-0.55));

// Panel (c): final formal sum. Four concrete copies of R plus Sq(CA).
pair O3=(12.0,0);
real rw=1.9, rh=1.05, gap=0.18;
for(int i=0;i<2;++i) for(int j=0;j<2;++j) {
  pair q=O3+(i*(rw+gap), j*(rh+gap)+1.25);
  filldraw(q--q+(rw,0)--q+(rw,rh)--q+(0,rh)--cycle, fillpen, mainpen);
  label("$R$",q+(rw/2,rh/2));
}
pair qsq=O3+(4.45,1.25);
filldraw(qsq--qsq+(2.1,0)--qsq+(2.1,2.1)--qsq+(0,2.1)--cycle, fillpen, mainpen);
label("$S_{CA}$", qsq+(1.05,1.05));
label("(c) final exact-scissors sum", O3+(3.25,5.05));
label("$4R+S_{CA}\sim_{\rm sc}S_{AD}$", O3+(3.25,-0.55));
label("$S_{BD}\sim_{\rm sc}S_{CB}$; II.7 on $B-C-A$", O3+(3.25,4.35));
