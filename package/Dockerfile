FROM ubuntu:focal

RUN apt-get update
# RUN env DEBIAN_FRONTEND=noninteractive apt-get --yes --no-install-recommends install tzdata
RUN apt-get --yes --no-install-recommends install software-properties-common dirmngr gpg-agent
# RUN add-apt-repository ppa:avsm/ppa
RUN apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
RUN echo "deb https://download.mono-project.com/repo/ubuntu stable-focal main" | tee /etc/apt/sources.list.d/mono-official-stable.list
RUN apt-get update
RUN apt-get --yes install --no-install-recommends opam emacs gcc binutils make m4 git time gnupg ca-certificates mono-devel
RUN useradd -d /home/test test
RUN mkdir /home/test
RUN chown test:test /home/test
RUN echo auth sufficient pam_succeed_if.so use_uid user = test > su.new
RUN cat /etc/pam.d/su >> su.new
RUN mv su.new /etc/pam.d/su

USER test
ENV HOME /home/test
WORKDIR $HOME
# RUN su -c echo test

SHELL ["/bin/bash", "--login", "-c"]

# Install OCaml
ENV OPAMYES 1
RUN opam init --disable-sandboxing --compiler=4.05.0
RUN opam env --set-switch | tee --append .profile .bashrc .bash_profile

# Clone and build Everest
ARG EVEREST_THREADS=1
RUN git clone https://github.com/project-everest/everest.git
WORKDIR everest
RUN ./everest --yes opam
RUN ./everest --yes pull
RUN ./everest --yes z3
RUN echo export PATH=$HOME/everest/z3/bin:$PATH | tee --append $HOME/.bash_profile $HOME/.profile $HOME/.bashrc
ENV FSTAR_HOME $HOME/everest/FStar
ENV KREMLIN_HOME $HOME/everest/kremlin
ENV QD_HOME $HOME/everest/quackyducky
ENV HACL_HOME $HOME/everest/hacl-star
ENV MLCRYPTO_HOME $HOME/everest/MLCrypto
ENV VALE_HOME $HOME/everest/vale
RUN env OTHERFLAGS='--admit_smt_queries true' ./everest -j $EVEREST_THREADS FStar make kremlin make quackyducky make
# RUN ./everest -j $EVEREST_THREADS MLCrypto make
RUN env OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2)) -C hacl-star vale-fst
RUN env OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2)) -C hacl-star compile-gcc-compatible
WORKDIR ..

WORKDIR quic-crypto
ADD src/*.fst src/*.fsti src/
ADD Makefile Makefile
ADD Makefile.include Makefile.include
ADD README.md README.md
ADD test/main.c test/QUICTest.fst test/Makefile test/
RUN su -c 'chown -R test:test src test Makefile* README.md'
RUN su -c 'chown test:test .'

ENTRYPOINT ["/bin/bash", "--login"]

