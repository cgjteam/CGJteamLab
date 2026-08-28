// equilateral_medians.asy
import CoxeterFiguresCommon;

size(10cm);

pair A = (0,0);
pair B = (6,0);
pair C = (3,3*sqrt(3));

pair MA = midpoint(B,C);
pair MB = midpoint(A,C);
pair MC = midpoint(A,B);

draw(A--B--C--cycle, mainpen);

draw(lineThrough(A,MA,0.18,0.22), axispen);
draw(lineThrough(B,MB,0.18,0.22), axispen);
draw(lineThrough(C,MC,0.18,0.22), axispen);

markPointLabel("$A$", A, SW);
markPointLabel("$B$", B, SE);
markPointLabel("$C$", C, N);

markPointLabel("$M_A$", MA, E);
markPointLabel("$M_B$", MB, NW);
markPointLabel("$M_C$", MC, S);

label("$a$", A + 0.55*(MA-A) + (-0.30,0.05), W);
label("$b$", B + 0.55*(MB-B) + (0.30,0.05), E);
label("$c$", C + 0.45*(MC-C) + (0.30,0.05), E);
