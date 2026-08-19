@echo off

for %%f in (Proposition??.tex) do pdflatex -interaction=nonstopmode -halt-on-error "%%f"
for %%f in (Proposition??.tex) do pdflatex -interaction=nonstopmode -halt-on-error "%%f"

pdflatex -interaction=nonstopmode -halt-on-error Book1R.tex
pdflatex -interaction=nonstopmode -halt-on-error Book1R.tex