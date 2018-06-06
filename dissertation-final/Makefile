LATEX="xelatex" -synctex=1 -interaction=nonstopmode -shell-escape 
BIBTEX=bibtex

all: acs-dissertation.pdf
acs-dissertation.pdf:  acs-dissertation.tex titlepage.tex declaration.tex abstract.tex MphilProject.bib
	$(LATEX) acs-dissertation
	$(BIBTEX) acs-dissertation
	$(LATEX) acs-dissertation
	$(LATEX) acs-dissertation

clean:
	$(RM) -f acs-dissertation.pdf acs-dissertation.ps acs-dissertation.dvi 
	$(RM) -f *.log *.aux *.toc *.bbl *.lot *.lof *.pdf

