CURRENT=paper

WGETDVANHORNBIB=curl -o dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

WGETIANJBIB=curl -o ianj.bib "http://www.citeulike.org/bibtex/user/ianjohnson?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

default: introspective-base.pdf introspective-lazy.pdf introspective-lazyc.pdf \
	 church-relative-space.pdf church-relative-time.pdf church-relative-speed.pdf \
	all-relative-space.pdf all-relative-speed.pdf all-relative-time.pdf \
	 bench-overview.tex
	xelatex $(CURRENT)

refresh: getbib

getbib:
	$(WGETDVANHORNBIB)
	$(WGETIANJBIB)
	-bibclean dvanhorn.bib > dvh-bibliography.bib.clean
	-bibclean ianj.bib > ianj.bib.clean
	cat ianj.bib.clean dvh-bibliography.bib.clean > bibliography.bib

bibtex:
	bibtex $(CURRENT)

%.dvi: %.tex
	latex $(basename $@)

all-relative-space.pdf: vis-bench.rkt
	racket vis-bench.rkt

all-relative-speed.pdf: vis-bench.rkt
	racket vis-bench.rkt

all-relative-time.pdf: vis-bench.rkt
	racket vis-bench.rkt

introspective-base.pdf: introspective-base.dot
	dot -Tpdf introspective-base.dot -o introspective-base.pdf

introspective-lazy.pdf: introspective-lazy.dot
	dot -Tpdf introspective-lazy.dot -o introspective-lazy.pdf

introspective-lazyc.pdf: introspective-lazyc.dot
	dot -Tpdf introspective-lazyc.dot -o introspective-lazyc.pdf

church-relative-speed.pdf: vardoulakis-shivers-numbers.rkt
	racket vardoulakis-shivers-numbers.rkt

church-relative-time.pdf: vardoulakis-shivers-numbers.rkt
	racket vardoulakis-shivers-numbers.rkt

church-relative-space.pdf: vardoulakis-shivers-numbers.rkt
	racket vardoulakis-shivers-numbers.rkt

bench-overview.tex:
	racket bench-overview.rkt

#%.pdf: %.dvi
#	dvipdfm -o $(basename $@).pdf $(basename $@).dvi

flush: clean
	rm -f dvanhorn.bib

clean:
	rm -f $(CURRENT).{dvi,ps,pdf,log,toc,blg,bbl,aux,rel} *.log *~ *.out


