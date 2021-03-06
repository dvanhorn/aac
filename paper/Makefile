CURRENT=paper
TARGET=sigplan
FILE=$(CURRENT)$(TARGET)
export TEXINPUTS := ./pfsteps:./mnsymbol:${TEXINPUTS}

BIBOPTS=fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:x-pages&volume:volume&fieldmap=publisher:x-publisher&fieldmap=series:x-series&fieldmap=editor:x-editor&fieldmap=isbn:x-isbn

WGETDVANHORNBIB=curl -o dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?$(BIBOPTS)"
WGETIANJOHNSONBIB=curl -o ianjohnson.bib "http://www.citeulike.org/bibtex/user/ianjohnson?$(BIBOPTS)"

default: $(FILE).tex #example0.pdf impl.pdf
	rubber -d $(FILE).tex

supp: proofs.tex
	rubber -d proofs.tex

show:
	xdg-open $(FILE).pdf

# Crude word-counting:
.PHONY: wc
wc:
	@wc -w abstract.tex
	@wc -w content.tex

#example0.pdf impl.pdf:
#	racket codes.rkt

# Open
open:
	xdg-open $(FILE).pdf

edit:
	emacs content.tex &

# Check style:
proof:
	echo "weasel words: "
	sh bin/weasel *.tex
	echo
	echo "passive voice: "
	sh bin/passive *.tex
	echo
	echo "duplicates: "
	perl bin/dups *.tex


# Forcibly refresh bibliography:
refresh: getbib

# Forcibly refresh bibliogaphy:
getbib:
	$(WGETDVANHORNBIB)
	$(WGETIANJOHNSONBIB)
	cat dvanhorn.bib ianjohnson.bib local.bib > bibliography.bib
	-bibclean bibliography.bib > bibliography.bib.clean
	-mv bibliography.bib.clean bibliography.bib

all:
	pdflatex $(FILE)
	bibtex $(FILE)
	pdflatex $(FILE)
	pdflatex $(FILE)

# Run bibtex:
bibtex:
	cat dvanhorn.bib ianjohnson.bib local.bib > bibliography.bib
	-bibclean bibliography.bib > bibliography.bib.clean
	-mv bibliography.bib.clean bibliography.bib
	bibtex $(FILE)


%.dvi: %.tex *.tex
	latex $(basename $@)

%.pdf: *.tex
	pdflatex $(FILE)

# %.pdf: %.dvi
#	dvipdfm -o $(basename $@).pdf $(basename $@).dvi


# Clean out net-fetched files:
flush: clean
	rm -f ianjohnson.bib

# Clean out local intermediate files:
clean:
	rm -f $(FILE).{dvi,ps,pdf,log,toc,blg,bbl,aux,rel} *.log *~
