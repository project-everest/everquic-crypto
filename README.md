# everquic-crypto

F\*/Low\* implementation of QUIC header and packet protection, verified
for memory safety, functional correctness and constant-time execution,
and compiled to C.

## tl;dr Summary

Should run on Linux (Ubuntu 18.04 and 20.04 are known to work.)

To verify the code and extract and compile the C code (if not already
present in `dist/`):

1. Install Project Everest (which includes F*) by running:
   `./install-everest.sh && source everest-env.sh`

   You may need to install OCaml and OPAM beforehand.

   Alternatively, if you do not want to make changes to your machine,
   you can build a Docker image using the provided `Dockerfile`, and
   work from within a container:
   `docker build -t everquic-crypto . && docker run -i -t everquic-crypto`

2. Run `make` to verify the proofs, extract the C code and build and
   run the test.

   Then, C files are produced in `dist/`.

   (You may need to run `make clean` beforehand if already produced
   before.)

Then, you can build dist/libeverquic.a by running:
`cd dist && make -f Makefile.basic`

## Structure of the proof

Our code is in `src/`. You can navigate it using the F* mode for Emacs
(https://github.com/FStarLang/fstar-mode.el), which is already
installed by default if you build the Docker image.

### Specifications and implementations using F* effects

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

### Constant-time execution

Our constant-time execution guarantees rely on data abstraction: more
precisely, for constant-time data we rely on abstract "secret" integer
types from HACL*
(https://github.com/project-everest/hacl-star/blob/master/lib/Lib.IntTypes.fsti).

#### Data abstraction: F* modules and interfaces

In F*, module definitions (`.fst`) may be hidden behind a
corresponding interface (`.fsti`), thus making their definitions
abstract.

Reading the actual value of a secret integer can be done only in ghost
computations, unless by explicit (unsafe) declassification using HACL*
`Lib.RawIntTypes`. Thus, our specifications in `QUIC.Spec.*` break
abstractions by virtue of being ghost, whereas our implementations in
`QUIC.Impl.*` respect type abstractions.

A module definition `B.fst` can break the abstractions of module `A`
by declaring `friend A`.For proof efficiency purposes, we split our
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

### Packet format

Following: https://quicwg.org/base-drafts/draft-ietf-quic-transport.html#name-packet-formats

The packet header format is split into two parts: the public part, and
the packet number:

* the format of the public part of the header, where the protected
  bits of the first byte are uninterpreted, is defined in
  `QUIC.Spec.Header.Public`. Corresponding parsers and formatters are
  implemented in `QUIC.Impl.Header.Public`.

* the packet number format is defined in `QUIC.Spec.PacketNumber` and
  its parser and formatter implemented in `QUIC.Impl.PacketNumber`.

* the format of the header, with the packet number, and the
  interpreted protected bits, is defined in `QUIC.Spec.Header.Parse`,
  and its parser and formatter are implemented in
  `QUIC.Impl.Header.Parse`.

### Header and packet protection

Following: https://quicwg.org/base-drafts/draft-ietf-quic-tls.html#name-packet-protection

Header protection, i.e. applying or removing protection on the packet
number field and the protected bits of the first byte of the packet,
is defined in `QUIC.Spec.Header`, and implemented in
`QUIC.Impl.Header`.

Header and packet protection, i.e. header protection plus
encryption/decryption of the packet payload, is defined in `QUIC.Spec`
and implemented in `QUIC.Impl`, using EverCrypt AEAD.

### QUIC transport state

In `QUIC.State`, we define a transport state that holds the AEAD state
and the current packet number, wrapped around header and packet
protection.

### Security proof

TODO: document model and switch
