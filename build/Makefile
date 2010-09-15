GRADE=java
JOBS=1
LINE_WIDTH=160
MERCURY_STD_LIB_DIR=

-include Make.params

MMC_MAKE_OPTS=-j$(JOBS) --grade $(GRADE) --use-grade-subdirs --halt-at-warn --max-error-line-width $(LINE_WIDTH)

.PHONY: vc
vc: Mercury.modules
	mmc --make $(MMC_MAKE_OPTS) vc

.PHONY: clean
clean:
	mmc --make vc.clean

.PHONY: realclean
realclean:
	mmc --make vc.realclean
	-rm -rf Mercury Mercury.modules

Mercury.modules:
	mmc -f `find ../src -name \*.m`


.PHONY: tags
tags:
	mtags `find .. $(MERCURY_STD_LIB_DIR) -name \*.m`
