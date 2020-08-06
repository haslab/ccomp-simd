FROM coqorg/coq:8.4.6

RUN sudo apt-get update && sudo apt-get install -y vim wget gcc-multilib

RUN opam install -y coq-mathcomp-algebra.1.6.1

RUN opam install -y menhir.20171222

RUN git clone https://github.com/coq-contribs/containers.git --branch v8.4 --single-branch

RUN (cd containers; make; make install; cd ..; rm -rf containers)

RUN wget http://compcert.inria.fr/release/compcert-2.2.tgz

RUN git clone https://github.com/haslab/ccomp-simd.git

RUN (cd ccomp-simd; tar xvzf ../compcert-2.2.tgz; make clean_setup_build_dir; cd build; ./configure ia32-linux; make depend; make)

