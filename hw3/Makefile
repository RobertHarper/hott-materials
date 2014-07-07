LATEXMK=latexmk
PDFTARGETS=hw3-handout hw3-solution

.PHONY: all clean
all:
	${LATEXMK} -pdf ${PDFTARGETS}

clean:
	${LATEXMK} -C ${PDFTARGETS}

