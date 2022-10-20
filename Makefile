all: test

test: dist/test.exe
	$<

# Boilerplate
# -----------

include Makefile.include

EXCLUDE_MODULES=Spec.Old Impl.Old

FST_FILES=$(filter-out $(addprefix src/QUIC.,$(addsuffix .fst,$(EXCLUDE_MODULES)) $(addsuffix .fsti,$(EXCLUDE_MODULES))),$(wildcard src/*.fst) $(wildcard src/*.fsti)) test/QUICTest.fst

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
	$(FSTAR) --codegen krml \
	--extract_module $(basename $(notdir $(subst .checked,,$<))) \
	$(notdir $(subst .checked,,$<))

verify: $(ALL_CHECKED_FILES)

# Karamel
# -------

KRML=$(KRML_HOME)/krml

obj/krml.rsp: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	for f in $^ ; do echo $$f ; done > $@

dist/Makefile.basic: obj/krml.rsp
	$(KRML) $(KOPTS) -library EverCrypt,EverCrypt.* @$^ -tmpdir dist -skip-compilation \
	  -minimal \
	  -header noheader.txt \
	  -add-include '"krml/internal/target.h"' \
	  -add-include '"krml/internal/types.h"' \
	  -add-include '"krml/lowstar_endianness.h"' \
	  -add-include '<stdint.h>' \
	  -add-include '<stdbool.h>' \
	  -add-include '<string.h>' \
	  -library 'Vale.Stdcalls.*' \
	  -no-prefix 'Vale.Stdcalls.*' \
	  -static-header 'Vale.Inline.*' \
	  -library 'Vale.Inline.X64.Fadd_inline' \
	  -library 'Vale.Inline.X64.Fmul_inline' \
	  -library 'Vale.Inline.X64.Fswap_inline' \
	  -library 'Vale.Inline.X64.Fsqr_inline' \
	  -no-prefix 'Vale.Inline.X64.Fadd_inline' \
	  -no-prefix 'Vale.Inline.X64.Fmul_inline' \
	  -no-prefix 'Vale.Inline.X64.Fswap_inline' \
	  -no-prefix 'Vale.Inline.X64.Fsqr_inline' \
	  -fparentheses \
	  -o libeverquic.a \
	  -bundle LowParse.* \
	  -bundle LowStar.* \
	  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=EverQuic_Krmllib] \
	  -bundle 'Meta.*,Hacl.*,Vale.*,Spec.*,Lib.*,EverCrypt,EverCrypt.*,NotEverCrypt.*[rename=EverQuic_EverCrypt]' \
	  -bundle Model.* \
	  -bundle Mem \
	  -bundle 'QUIC.State+QUIC.Impl.Header.Base=QUIC.\*[rename=EverQuic,rename-prefix]'

dist/libeverquic.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

.PHONY: clean clean-dist verify

# Tests
# -----

CFLAGS+=-I$(realpath .)/dist -I$(realpath $(KRML_HOME))/include -I$(realpath $(KRML_HOME))/krmllib/dist/minimal
export CFLAGS

test/main.o: dist/Makefile.basic

dist/test.exe: test/main.o dist/libeverquic.a $(HACL_HOME)/dist/gcc-compatible/libevercrypt.a $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a
	$(CC) $^ -o $@
