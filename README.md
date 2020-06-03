# everquic-crypto

F\*/Low\* implementation of QUIC header and packet protection, verified
for memory safety, functional correctness and constant-time execution,
and compiled to C.

## How to verify, extract and build

EverQuic is implemented in F* in `src/`, and extracted to C in
`dist/EverQuic.c` and `dist/EverQuic.h`. Then, you can build the
EverQuic static library, `dist/libeverquic.a`, by running: `cd dist &&
make -f Makefile.basic`

If `dist/EverQuic.c` and `dist/EverQuic.h` are not present, then you
will need to regenerate them by verifying the F* code and extracting
the C code as follows (Ubuntu 18.04 and 20.04 are known to work):

1. Install Project Everest (which includes F*) by running:
   `./install-everest.sh && source everest-env.sh`

   You can set the `EVEREST_THREADS` environment variable to set some
   parallelism factor.

   You may need to install Mono, OCaml (>= 4.05, < 4.10) and OPAM
   beforehand.

   Alternatively, if you do not want to make changes to your machine,
   you can build a Docker image using the provided `Dockerfile`, and
   work from within a container:
   `docker build -t everquic-crypto . && docker run -i -t everquic-crypto`
   You can set the `EVEREST_THREADS` build-arg to set some parallelism factor.

2. Run `make` to verify the proofs, extract the C code and build and
   run the test.

   Then, C files are produced in `dist/`.

## Prelude: F* and formal guarantees

### F* effects: memory-safety, type-safety and functional correctness

We are using three classes of F* effects:

* Stateful computations (`ST`/`Stack`): concrete values and functions
  with side effects (memory accesses), compiled to C

* Pure computations (`Tot`/`Pure`): concrete values and functions
  without side effects, compiled to C

* Ghost computations (`GTot`/`Ghost`): values and functions for proof
  purposes only, erased from the C code

In our code, we adopt the convention that `QUIC.Spec.*` modules define
specifications as ghost computations, whereas `QUIC.Impl.*` modules
define their corresponding pure or stateful implementations.

F* type-checking ensures both memory-safety and type-safety. In
addition, the types of the `QUIC.Impl.*` implementations, as
Hoare-style pre- and postconditions, mention the specifications in
`QUIC.Spec.*` to ensure functional correctness.

### Constant-time execution

Our constant-time execution guarantees rely on data abstraction: more
precisely, for constant-time data we rely on abstract "secret" integer
types from HACL*
(https://github.com/project-everest/hacl-star/blob/master/lib/Lib.IntTypes.fsti).

#### Data abstraction: F* modules and interfaces

In F*, module definitions (`.fst`) may be hidden behind a
corresponding interface (`.fsti`), thus making their definitions
abstract. There, the `.fsti` contains the signatures of the functions
implemented (and the statements of the theorems proven) in the `.fst`
that are meant to be directly callable by client code.

Reading the actual value of a secret integer can be done only in ghost
computations, unless by explicit (unsafe) declassification using HACL*
`Lib.RawIntTypes`. Thus, by virtue of being ghost, our specifications
in `QUIC.Spec.*` safely "read" secret integer values for proof
purposes only, whereas our implementations in `QUIC.Impl.*` respect
type abstractions.

A module definition `B.fst` can break the abstractions of module `A`
by declaring `friend A`. For proof efficiency purposes, we split our
code in such a way that `QUIC.Impl.Foo` only needs to expose the
definitions from `QUIC.Spec.Foo`. However, we are careful not to use
`friend` in our code for secret data types.

#### Operations on secret data

`QUIC.Secret.Int` defines constant-time operations on secret integers,
including comparisons (whose results are secret, in such a way that
one cannot branch on them with `if`).

`QUIC.Secret.Seq` defines operations on sequences of secret data.

`QUIC.Secret.Buffer` defines an abstraction construct for a code block
to use a buffer (F\*/Low\* representation of a C array) of public
integers as a buffer of secret integers (but not the converse).

## Implementation

### Packet format

Following: https://quicwg.org/base-drafts/draft-ietf-quic-transport.html#name-packet-formats

The packet header format is split into two parts: the public part, and
the packet number. The parser and formatter specifications and
implementations use EverParse.

* The C data type for QUIC packet headers is defined in
  `QUIC.Impl.Header.Base` as type `header`, and extracted as the
  `EverQuic_header` type definition in `dist/EverQuic.h`.

* the format of the public part of the header, where the protected
  bits of the first byte are uninterpreted, is defined in
  `QUIC.Spec.Header.Public`. Corresponding parsers and formatters are
  implemented in `QUIC.Impl.Header.Public`.

* the packet number format is defined in `QUIC.Spec.PacketNumber` and
  its parser and formatter implemented in
  `QUIC.Impl.PacketNumber`. Most notably,
  `QUIC.Spec.PacketNumber.expand_pn'` specifies packet number
  expansion, which is implemented in
  `QUIC.Impl.Packet_number.expand_pn_aux` in a constant-time way. The
  latter function is extracted as `expand_pn` in `dist/EverQuic.c`.

* the format of the header, with the packet number, and the
  interpreted protected bits, is defined in `QUIC.Spec.Header.Parse`,
  and its parser and formatter are implemented in
  `QUIC.Impl.Header.Parse`. The parser is implemented as
  `QUIC.Impl.Header.read_header`, extracted as `read_header0` in
  `dist/EverQuic.c`; the formatter is implemented as
  `QUIC.Impl.Header.write_header`, extracted as `write_header0` in
  `dist/EverQuic.c`.

### Header and packet protection

Following: https://quicwg.org/base-drafts/draft-ietf-quic-tls.html#name-packet-protection

Header protection, i.e. applying or removing protection on the packet
number field and the protected bits of the first byte of the packet,
is defined in `QUIC.Spec.Header`, and implemented in
`QUIC.Impl.Header`, as `header_encrypt` to apply protection and
`header_decrypt` to remove protection. They are extracted under these
names in `dist/EverQuic.c`.

Header and packet protection, i.e. header protection plus
encryption/decryption of the packet payload, is defined in `QUIC.Spec`
and implemented in `QUIC.Impl`, using EverCrypt AEAD, as `encrypt` to
apply protection and `decrypt` to remove protection. They are
extracted under these names in `dist/EverQuic.c`.

### QUIC transport state

In `QUIC.State`, we define a transport state type, `state_s`, that
holds the AEAD state and the number of the last packet sent or
received. This state, extracted as `EverQuic_state_s` in
`dist/EverQuic.h`, is wrapped around header and packet
protection. There, `create_in` allocates and creates a state,
`encrypt` applies protection and `decrypt` removes protection. Those
functions are extracted as `EverQuic_create_in`, `EverQuic_encrypt`
and `EverQuic_decrypt` respectively, in `dist/EverQuic.h` and
`dist/EverQuic.c`.

## Security proof

TODO: document model and switch
