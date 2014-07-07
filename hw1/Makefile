LATEXMK=latexmk
PDFTARGETS=hw1-handout hw1-solution

.PHONY: all clean
all:
	${LATEXMK} -pdf ${PDFTARGETS}

clean:
	${LATEXMK} -C ${PDFTARGETS}

