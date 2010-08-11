GRADE=java
JOBS=1
LINE_WIDTH=160

-include Make.params

MMC_MAKE_OPTS=--grade $(GRADE) --use-grade-subdirs --max-error-line-width $(LINE_WIDTH)

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


