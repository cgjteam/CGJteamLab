// perpendicular_axes_p2.asy
import CoxeterFiguresCommon;

size(9cm);

pair O = (0,0);
pair U = (3.0,0);
pair V = (0,2.6);

path l1 = (-4.2,0) -- (4.2,0);
path l2 = (0,-3.6) -- (0,3.6);

draw(l1, axispen);
draw(l2, axispen);

draw((0.36,0)--(0.36,0.36)--(0,0.36), mainpen);

markPointLabel("$O$", O, SW);
markPointLabel("$U$", U, S);
markPointLabel("$V$", V, E);

label("$l_1$", (4.2,0), E);
label("$l_2$", (0,3.6), N);
