LATEXMK=latexmk
PDFTARGETS=hw4-handout hw4-solution

.PHONY: all clean
all:
	${LATEXMK} -pdf ${PDFTARGETS}

clean:
	${LATEXMK} -C ${PDFTARGETS}

