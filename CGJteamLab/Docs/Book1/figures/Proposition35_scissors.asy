import graph;
size(12cm);

real ystep = -5.4;

// ------------------------------------------------------------
// Panel 1: ABCD + DGE
// ------------------------------------------------------------
void panelLeftAug(pair O)
{
  // tu wklejasz obecny kod dawnego leftAug(O)
  // tylko bez zmian geometrycznych
  label("$ABCD + DGE$", O + (3.6,2.9));
}

// ------------------------------------------------------------
// Panel 2: EAB + GBC
// ------------------------------------------------------------
void panelLeftRefined(pair O)
{
  // tu wklejasz obecny kod dawnego leftRefined(O)
  label("$EAB + GBC$", O + (3.6,2.9));
}

// ------------------------------------------------------------
// Panel 3: FDC + GBC
// ------------------------------------------------------------
void panelRightRefined(pair O)
{
  // tu wklejasz obecny kod dawnego rightRefined(O)
  label("$FDC + GBC$", O + (3.6,2.9));
}

// ------------------------------------------------------------
// Panel 4: EBCF + DGE
// ------------------------------------------------------------
void panelRightAug(pair O)
{
  // tu wklejasz obecny kod dawnego rightAug(O)
  label("$EBCF + DGE$", O + (3.6,2.9));
}

// ------------------------------------------------------------
// Layout pionowy
// ------------------------------------------------------------
pair P0 = (0,0);
pair P1 = (0,ystep);
pair P2 = (0,2*ystep);
pair P3 = (0,3*ystep);

panelLeftAug(P0);
panelLeftRefined(P1);
panelRightRefined(P2);
panelRightAug(P3);

// przejście 1
draw((4.2,-2.2)--(4.2,ystep+3.9), black+0.9bp, Arrow);
label("split / regroup", (4.5,(ystep+1.7)), E);

// przejście 2
draw((4.2,ystep-2.2)--(4.2,2*ystep+3.9), black+0.9bp, Arrow);
label("replace congruent outer triangle", (4.5,(1.5*ystep+0.9)), E);

// przejście 3
draw((4.2,2*ystep-2.2)--(4.2,3*ystep+3.9), black+0.9bp, Arrow);
label("reverse split / regroup", (4.5,(2.5*ystep+0.9)), E);