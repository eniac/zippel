all: grammar.pdf

grammar.pdf: grammar.tex
	pdflatex $<

grammar.tex: grammar.ott
	ott -colour false -tex_show_meta false -i $< -o $@
clean:
	-rm -f grammar.tex grammar.pdf grammar.aux grammar.log

.PHONY: all
