.PHONY: main notes clean submit arxiv # otherwise confused by folders with the same name

default: main

main: main.pdf
notes: notes.pdf

# -out2dir unsupported on default Mac installation
LATEXMK_OPTS:=-output-format=pdf -outdir=_latex
export BIBINPUTS=..:

MAIN_DEPS:=$(wildcard main/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

main.pdf: main.tex $(MAIN_DEPS)
	latexmk $(LATEXMK_OPTS) main
	cd _latex && bibtex main
	latexmk $(LATEXMK_OPTS) -g main
	cp _latex/main.pdf .
	@! grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/main.log

NOTES_DEPS:=$(wildcard notes/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

notes.pdf: notes.tex $(NOTES_DEPS)
	latexmk $(LATEXMK_OPTS) notes
	cd _latex && bibtex notes
	latexmk $(LATEXMK_OPTS) -g notes
	cp _latex/notes.pdf .
	@! grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/notes.log

AGDA_EXCLUDES:=-x "agda/_build/*" -x "agda/src/unused/*" -x "agda/src/incomplete/*"

submit: main-submit.pdf
	cd agda && agda src/everything.agda
	rm -f suppl-submit.zip
	zip -r suppl-submit.zip agda $(AGDA_EXCLUDES)
	@if grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/main-submit.log; then \
		echo "submit: main-submit.pdf has undefined references/citations (suppl-submit.zip still built):" >&2; \
		grep -aE "undefined" _latex/main-submit.log | grep -aoE "(Reference|Citation) .[^']*'" | sort -u >&2; \
		exit 1; \
	fi

main-submit.pdf: main-submit.tex main.tex $(MAIN_DEPS)
	latexmk $(LATEXMK_OPTS) main-submit
	cd _latex && bibtex main-submit
	latexmk $(LATEXMK_OPTS) -g main-submit
	cp _latex/main-submit.pdf .

arxiv: main.pdf
	@if grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/main.log; then \
		echo "arxiv: main.pdf has undefined references/citations; not building arXiv.zip:" >&2; \
		grep -aE "undefined" _latex/main.log | grep -aoE "(Reference|Citation) .[^']*'" | sort -u >&2; \
		exit 1; \
	fi
	rm -f arXiv.zip
	git ls-files | zip arXiv.zip -@

clean:
	rm -rf _latex
	rm -f main.pdf
	rm -f main-submit.pdf
	rm -f suppl-submit.zip
	rm -f arXiv.zip
	rm -f notes.pdf
