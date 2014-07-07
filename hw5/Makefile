LATEXMK=latexmk
PDFTARGETS=hw5-handout hw5-solution

.PHONY: all clean
all:
	${LATEXMK} -pdf ${PDFTARGETS}

clean:
	${LATEXMK} -C ${PDFTARGETS}

