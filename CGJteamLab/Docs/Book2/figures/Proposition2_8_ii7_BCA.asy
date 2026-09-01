// Euclid II.8 - the imported II.7 normal form on the reversed cut B-C-A.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(14cm,0);

defaultpen(fontsize(10pt));
pen mainpen = black + linewidth(0.9);
pen fillA = gray(0.95);
pen fillB = gray(0.90);

void box(pair O, real w, real h, pen p, string lab) {
  filldraw(O--O+(w,0)--O+(w,h)--O+(0,h)--cycle, p, mainpen);
  label(lab, O+(w/2,h/2));
}

// Schematic exact-scissors normal form.  It is not asserted to be a single
// literal planar dissection; it records the already proved II.7 identity.

// Left side: W + S_CB.
pair L=(0,0);
box(L,3.3,3.3,fillA,"$W=\mathrm{Sq}(BA)$");
box(L+(3.8,0.65),2.0,2.0,fillB,"$S_{CB}$");
label("$+$", L+(3.55,1.65));

// Equality sign.
label("$\simeq_{\rm sc}$", (7.05,1.65));

// Right side: R + R + S_CA.
pair R0=(8.3,0.15);
box(R0,2.4,1.45,fillB,"$R$");
box(R0+(0,1.75),2.4,1.45,fillB,"$R$");
box(R0+(2.9,0.55),2.15,2.15,fillA,"$S_{CA}$");
label("$+$", R0+(2.65,1.65));

label("II.7 on the reversed cut $B-C-A$", (6.55,4.35));
label("the same $W$ and the same rectangle term $R$ are reused", (6.55,-0.55), S);
