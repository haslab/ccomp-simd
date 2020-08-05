# CircGen - Circuit Description Generation tool

This is a prototype of the **ccomp-simd** tool -- an extension of the
*CompCert - a certified compiler for C*
(http://compcert.inria.fr) supporting vector instructions on the `x64`
architecture. Please refer to the original CompCert's
[README](README) and its [manual](http://compcert.inria.fr/man/) for
addition information on CompCert on its copyright/usage instructions.

The current prototype also inlcudes an intrinsics-aware constant-time
checker, based on a fine-grained type system that assigns a security types
at each program point and calling context to each location (registe
or memory location).



## Instalation

The original version of this development have been completed in 2016,
and hence relies on fairly old version of the supporting
tools<sup>[1](#myfootnote1)</sup>. Specifically, it depends on the
following packages/versions:

 * [Python3](http://python.org)
 * [Ocaml](https://ocaml.org) functional language (version 4.02.3)
 * [Coq](https://coq.inria.fr) proof assistant (version 8.4.6)
 * [coq-contrib/containers](https://github.com/coq-contribs/containers/tree/v8.4) (for coq v8.4)
 * [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser
   generator (version 20171222)
 * [SsReflect](http://ssr.msr-inria.inria.fr) Ssreflect/MathComp (version 1.6.1)

Most of the above packages are available through the
[OPAM](https://opam.ocaml.org) (Ocaml Package Manager).

```
opam install coq.8.4.6
opam install menhir.20171222
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-algebra.1.6.1
```

Alternatively, a [Dockerfile](scripts/Dockerfile) is included that prepares a
[Docker](https://www.docker.com) container preloaded with the required dependencies.


### Clone the repository

The `ccomp-simd` tool reposity includes the CompCert repository as a submodule.
In order to clone it (including CompCert's repo) please perform:

```bash
$ git clone --recursive https://github.com/haslab/CircGen.git
$ cd circgen
```

### Preparing the `build` directory

The tool is compiled in a dedicated `build` directory that only has
links to both CompCert's and CircGen's source files. The toplevel `Makefile`
includes a target to setup the `build` directory.

```bash
$ make clean_setup_build_dir
$ cd build
```

### Compilation

To compile the tool, please execute ($OS is either `macosx` or `linux`):

```bash
$ ./configure bool-circ-$OS
$ make depend
$ make
```

## Examples

Directory `./tests/bcircuits` includes several examples on the usage of
the tool. These examples include standard SMC test circuits, such as
the AES symmetric cipher or the SHA-256 compression function.




---

<a name="myfootnote1">1</a>: Porting the development to the current versions of the support tools is in progress.
