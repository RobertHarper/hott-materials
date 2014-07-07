LATEXMK=latexmk
PDFTARGETS=hw2-handout hw2-solution

.PHONY: all clean
all:
	${LATEXMK} -pdf ${PDFTARGETS}

clean:
	${LATEXMK} -C ${PDFTARGETS}

