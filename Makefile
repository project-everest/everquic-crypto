all: test

test: dist/test.exe
	$<

# Boilerplate
# -----------

include Makefile.include

FST_FILES=$(wildcard src/*.fst) $(wildcard src/*.fsti)

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	@mkdir -p obj
	@$(FSTAR) --dep full $(FST_FILES) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

clean-dist:
	rm -rf dist

clean: clean-dist
	rm -rf obj .depend

# Verification
# ------------

%.checked:
	$(FSTAR) --hint_file hints/$(notdir $*).hints $(notdir $*) && touch -c $@

%.krml:
	$(FSTAR) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<))) \
	$(notdir $(subst .checked,,$<))

verify: $(ALL_CHECKED_FILES)

# Kremlin
# -------

KRML=$(KREMLIN_HOME)/krml

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $(KOPTS) -library EverCrypt,EverCrypt.* $^ -tmpdir dist -skip-compilation \
	  -minimal \
	  -add-include '"kremlin/internal/target.h"' \
	  -add-include '"kremlin/internal/types.h"' \
	  -add-include '"kremlin/lowstar_endianness.h"' \
	  -add-include '<stdint.h>' \
	  -add-include '<stdbool.h>' \
	  -add-include '<string.h>' \
	  -fparentheses \
	  -o libeverquic.a \
	  -bundle LowParse.* \
	  -bundle LowStar.* \
	  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=EverQuic_Kremlib] \
	  -bundle 'Meta.*,Hacl.*,Vale.*,Spec.*,Lib.*,EverCrypt,EverCrypt.*[rename=EverQuic_EverCrypt]' \
	  -bundle 'QUIC.Impl=QUIC.*[rename=EverQuic]'

dist/libeverquic.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

.PHONY: clean clean-dist verify

# Tests
# -----

CFLAGS+=-I$(realpath .)/dist -I$(realpath $(KREMLIN_HOME))/include
export CFLAGS

dist/test.exe: test/main.o dist/libeverquic.a $(HACL_HOME)/dist/compact-gcc/libevercrypt.a $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
	$(CC) $^ -o $@
