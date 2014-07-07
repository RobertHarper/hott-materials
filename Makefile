SUBDIRS=hw1 hw2 hw3 hw4 hw5 notes

.PHONY: all clean
all:
	for subdir in ${SUBDIRS} ; do \
		$(MAKE) -C $$subdir all ; \
	done

clean:
	for subdir in ${SUBDIRS} ; do \
		$(MAKE) -C $$subdir clean ; \
	done
