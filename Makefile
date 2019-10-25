all: verify

include $(HACL_HOME)/Makefile.include

FSTAR_INCLUDE_PATH= \
	obj \
	src \
	$(KREMLIN_HOME)/kremlib \
	$(ALL_HACL_DIRS) \


FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
	$(addprefix --include ,$(FSTAR_INCLUDE_PATH)) \
	--already_cached '*,-QUIC' \
	--cache_checked_modules \
	--cache_dir obj \
	--odir obj \
	--use_hints \
	--warn_error @241 \
	$(OTHERFLAGS)

FST_FILES=$(wildcard src/*.fst) $(wildcard src/*.fsti)

obj/.depend: $(FST_FILES)
	mkdir -p obj
	$(FSTAR) --dep full $^ > $@

-include obj/.depend

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) --hint_file hints/$(notdir $*).hints $<

verify: $(ALL_CHECKED_FILES)

clean:
	rm -rf obj

.PHONY: all verify clean
