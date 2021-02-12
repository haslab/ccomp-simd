# **ccomp-simd** - ARM SIMD extensions for CompCert


This is a(n incomplete) prototype of the ARM **ccomp-simd** tool -- an extension of the
*CompCert - a certified compiler for C*
(http://compcert.inria.fr) supporting vector instructions on the `ARM/NEON`
architecture. Please refer to the original CompCert's
[README](README) and its [manual](http://compcert.inria.fr/man/) for
addition information on CompCert and on its copyright/usage instructions.

---

## Installation

The original version of this development have been coded in 2016,
and hence relies on fairly old versions of the supporting
tools. Specifically, it depends on the
following packages/versions:

 * [Python3](http://python.org)
 * [Ocaml](https://ocaml.org) functional language (version 4.02.3)
 * [Coq](https://coq.inria.fr) proof assistant (version 8.4.6)
 * [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser
   generator (version 20171222)
 * [SsReflect](http://ssr.msr-inria.inria.fr) Ssreflect/MathComp (version 1.6.1)
 * [gcc-arm-linux-gnueabihf] -- arm cross-compiler

### Alternative #1: use [Docker](https://www.docker.com)

The simplest way of experimenting with **ccomp-simd** is by resorting to a _Docker_ container that includes all the mentioned packages. A [Dockerfile](scripts/Dockerfile) is provided for it:

```
docker build https://raw.githubusercontent.com/haslab/ccomp-simd/master/scripts/Dockerfile
```

The build process creates a _docker_ container with all the required packages and the (pre-compiled) **ccomp**.

