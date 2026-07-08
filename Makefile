.PHONY: main notes clean submit check-agda # otherwise confused by folders with the same name

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

# --- Submission bundle -------------------------------------------------------

SUBMISSION_DIR:=_submission
# Exclude build artifacts and code not part of the development from the supplement.
AGDA_EXCLUDES:=-x "agda/_build/*" -x "agda/src/unused/*" -x "agda/src/incomplete/*"

# Anonymous, review-mode (line-numbered), change-markup-free PDF plus the Agda
# development, gated on everything.agda typechecking.
submit: check-agda main-submit.pdf
	rm -rf $(SUBMISSION_DIR)
	mkdir -p $(SUBMISSION_DIR)
	cp main-submit.pdf $(SUBMISSION_DIR)/paper.pdf
	zip -r $(SUBMISSION_DIR)/suppl.zip agda $(AGDA_EXCLUDES)

check-agda:
	cd agda && agda src/everything.agda

main-submit.pdf: main-submit.tex main.tex $(MAIN_DEPS)
	latexmk $(LATEXMK_OPTS) main-submit
	cd _latex && bibtex main-submit
	latexmk $(LATEXMK_OPTS) -g main-submit
	cp _latex/main-submit.pdf .
	@! grep -qE "LaTeX Warning: There were undefined references\.|natbib Warning: There were undefined citations\." _latex/main-submit.log

clean:
	rm -rf _latex
	rm -rf $(SUBMISSION_DIR)
	rm -f main.pdf
	rm -f main-submit.pdf
	rm -f notes.pdf
