all: dist/libeverquic.a

# Boilerplate
# -----------

include $(HACL_HOME)/Makefile.include

FSTAR_INCLUDE_PATH= \
	src \
	$(KREMLIN_HOME)/kremlib \
	$(ALL_HACL_DIRS) \


FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
	$(addprefix --include ,$(FSTAR_INCLUDE_PATH)) \
	--already_cached '*,-QUIC' \
	--cache_checked_modules \
	--cache_dir obj \
	--odir obj \
	--cmi \
	--use_hints \
	--warn_error @241 \
	$(OTHERFLAGS)

FST_FILES=$(wildcard src/*.fst) $(wildcard src/*.fsti)

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	mkdir -p obj
	$(FSTAR) --dep full $(FST_FILES) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

clean-dist:
	rm -rf dist

clean: clean-dist
	rm -rf obj

# Verification
# ------------

%.checked:
	$(FSTAR) --hint_file hints/$(notdir $*).hints $< && touch -c $@

%.krml:
	$(FSTAR) --codegen Kremlin \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    $(notdir $(subst .checked,,$<))

# Kremlin
# -------

KRML=$(KREMLIN_HOME)/krml

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $(KOPTS) -library EverCrypt,EverCrypt.* $^ -tmpdir dist -skip-compilation \
	  -minimal \
	  -add-include '"kremlin/internal/target.h"' \
	  -add-include '<stdint.h>' \
	  -add-include '<stdbool.h>' \
	  -add-include '<string.h>' \
	  -o libeverquic.a \
	  -bundle LowStar.* \
	  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=EverQuic_Kremlib] \
	  -bundle 'Meta.*,Hacl.*,Vale.*,Spec.*,Lib.*,EverCrypt,EverCrypt.*[rename=EverQuic_EverCrypt]' \
	  -bundle 'QUIC.Impl=QUIC.*[rename=EverQuic]'

dist/libeverquic.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

.PHONY: clean
