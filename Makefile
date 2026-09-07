.PHONY: main examples notes mu-types check clean submit arXiv # otherwise confused by folders with the same name

default: check main

# Type-check the development and compare the regenerated artefacts with their baselines. The stamp
# skips the check when no source, script or baseline has changed since it last passed.
CHECK_DEPS:=$(shell find agda/src -name '*.agda') $(wildcard script/*.sh) $(wildcard test-baselines/*) $(wildcard dot/*)

check: agda/_build/check.stamp

agda/_build/check.stamp: $(CHECK_DEPS)
	cd agda && agda src/everything.agda
	script/check.sh
	touch $@

main: main.pdf
examples: examples.pdf
notes: notes.pdf
mu-types: mu-types.pdf

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

MU_TYPES_DEPS:=$(wildcard mu-types/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

mu-types.pdf: mu-types.tex $(MU_TYPES_DEPS)
	latexmk $(LATEXMK_OPTS) mu-types
	cd _latex && bibtex mu-types
	latexmk $(LATEXMK_OPTS) -g mu-types
	cp _latex/mu-types.pdf .
	@! grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/mu-types.log

examples.pdf: examples.tex $(wildcard test-baselines/matrices/*.tex)
	latexmk $(LATEXMK_OPTS) examples
	cp _latex/examples.pdf .

NOTES_DEPS:=$(wildcard notes/*.tex) $(wildcard fig/*.tex) macros.tex bib.bib

notes.pdf: notes.tex $(NOTES_DEPS)
	latexmk $(LATEXMK_OPTS) notes
	cd _latex && bibtex notes
	latexmk $(LATEXMK_OPTS) -g notes
	cp _latex/notes.pdf .
	@! grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/notes.log

AGDA_EXCLUDES:=-x "agda/_build/*" -x "agda/src/unused/*" -x "agda/src/incomplete/*" -x "agda/src/*~"

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

arXiv: main.pdf
	@if [ -n "$$(git status --porcelain)" ]; then \
		echo "arXiv: uncommitted changes; arXiv.zip is built from HEAD, so commit (or stash) first:" >&2; \
		git status --short >&2; \
		exit 1; \
	fi
	@if grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/main.log; then \
		echo "arXiv: main.pdf has undefined references/citations; not building arXiv.zip:" >&2; \
		grep -aE "undefined" _latex/main.log | grep -aoE "(Reference|Citation) .[^']*'" | sort -u >&2; \
		exit 1; \
	fi
	rm -f arXiv.zip
	git archive --format=zip HEAD -o arXiv.zip

clean:
	rm -rf _latex
	rm -f main.pdf
	rm -f main-submit.pdf
	rm -f suppl-submit.zip
	rm -f arXiv.zip
	rm -f notes.pdf
	rm -f examples.pdf
	rm -f mu-types.pdf
