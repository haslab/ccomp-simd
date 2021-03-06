# **ccomp-simd** - SIMD extensions for CompCert

This is a prototype of the **ccomp-simd** tool -- an extension of the
*CompCert - a certified compiler for C*
(http://compcert.inria.fr) supporting vector instructions on the `x64`
architecture. Please refer to the original CompCert's
[README](README) and its [manual](http://compcert.inria.fr/man/) for
addition information on CompCert and on its copyright/usage instructions.

The current prototype includes also an intrinsics-aware constant-time
checker, based on a fine-grained type system that assigns security
types to each location (register or memory location) at each program
point and calling context.

---

## Installation

The original version of this development have been completed in 2016,
and hence relies on fairly old versions of the supporting
tools<sup>[1](#myfootnote1)</sup>. Specifically, it depends on the
following packages/versions:

 * [Python3](http://python.org)
 * [Ocaml](https://ocaml.org) functional language (version 4.02.3)
 * [Coq](https://coq.inria.fr) proof assistant (version 8.4.6)
 * [coq-contrib/containers](https://github.com/coq-contribs/containers/tree/v8.4) (coq v8.4 contribs)
 * [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser
   generator (version 20171222)
 * [SsReflect](http://ssr.msr-inria.inria.fr) Ssreflect/MathComp (version 1.6.1)

### Alternative #1: use [Docker](https://www.docker.com)

The simplest way of experimenting with **ccomp-simd** is by resorting to a _Docker_ container that includes all the mentioned packages. A [Dockerfile](scripts/Dockerfile) is provided for it:

```
docker build https://raw.githubusercontent.com/haslab/ccomp-simd/master/scripts/Dockerfile
```

The build process creates a _docker_ container with all the required packages and the (compiled) **ccomp_simd** tool.

### Alternative #2: manual installation

#### step 1: install dependencies

Otherwise, one should install the dependencies manually. Most of the packages are available through the [OPAM](https://opam.ocaml.org) (Ocaml Package Manager), namelly:

```
opam install coq.8.4.6
opam install menhir.20171222
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-algebra.1.6.1
```

(obs: the _containers_ coq plugin should be compiled/installed from the _github_ link given above).

#### step 2: clone the repository and fetch the _compcert_ compiler

```bash
$ git clone https://github.com/haslab/ccomp-simd.git
$ wget http://compcert.inria.fr/release/compcert-2.2.tgz
$ cd ccomp_simd
$ tar xvzf ../compcert-2.2.tgz
```

#### step 3: prepare the `build` directory and compile the tool

The tool is compiled in a dedicated `build` directory that only has
links to both CompCert's and ccomp-simd's source files. The toplevel `Makefile`
includes a target to setup the `build` directory.

```bash
$ make clean_setup_build_dir
$ cd build
$ ./configure ia32-$OS
$ make depend
$ make
```
where `$OS` is either `macosx` or `linux`.


---

## Summary of Changes

| component     |  files affected  | modified/added lines |
| ------------- | ---------------- | -------------------- |
| backend       | 26               | 795                  |
| cfrontend     | 12               | 166                  |
| common        | 6                | 76                   |
| cparser       | 11               | 191                  |
| driver        | 5                | 159                  |
| extraction    | 1                | 13                   |
| lib           | 2                | 28                   |
| ia32          | 22               | 4886                 |
| taintanalysis | 27               | 8859                 |
| tools         | 2                | 3311                 |

---

<a name="myfootnote1">1</a>: The port of the development to the current versions of the supporting tools is in progress.
