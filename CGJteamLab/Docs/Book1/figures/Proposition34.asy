import graph;
size(10cm,0);

pair A=(0,2.2);
pair B=(4.4,2.2);
pair C=(5.4,0);
pair D=(1.0,0);

pen sidepen = linewidth(0.9);
pen diagpen = linewidth(0.8)+dashed;

draw(A--B--C--D--cycle, sidepen);
draw(A--C, diagpen);

dot(A); dot(B); dot(C); dot(D);
label("$A$", A, NW);
label("$B$", B, NE);
label("$C$", C, SE);
label("$D$", D, SW);

void slash(pair p, pair dir) {
  pair n=unit((-dir.y,dir.x));
  draw(p-0.10*n--p+0.10*n, linewidth(0.8));
}

pair mab=(A+B)/2;
pair mcd=(C+D)/2;
pair mbc=(B+C)/2;
pair mda=(D+A)/2;

slash(mab, B-A);
slash(mcd, D-C);

slash(mbc+0.08*unit(B-C), C-B);
slash(mbc-0.08*unit(B-C), C-B);
slash(mda+0.08*unit(D-A), A-D);
slash(mda-0.08*unit(D-A), A-D);
