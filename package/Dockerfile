FROM ubuntu

RUN apt-get update
# RUN env DEBIAN_FRONTEND=noninteractive apt-get --yes --no-install-recommends install tzdata
RUN apt-get --yes --no-install-recommends install software-properties-common
# RUN add-apt-repository ppa:avsm/ppa
RUN apt-get --yes install --no-install-recommends opam emacs gcc binutils make m4
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
RUN su -c 'apt-get --yes install git'
RUN git clone https://github.com/project-everest/everest.git
WORKDIR everest
RUN ./everest --yes opam
RUN ./everest --yes pull
RUN ./everest --yes z3
RUN env OTHERFLAGS='--admit_smt_queries true' ./everest -j $EVEREST_THREADS FStar make kremlin make quackyducky make
RUN su -c 'apt-get install --no-install-recommends --yes time gnupg ca-certificates'
RUN su -c 'apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF'
RUN echo "deb https://download.mono-project.com/repo/ubuntu stable-bionic main" | su -c 'tee /etc/apt/sources.list.d/mono-official-stable.list'
RUN su -c 'apt-get update'
RUN su -c 'apt-get install --no-install-recommends --yes mono-devel'
#RUN env OTHERFLAGS='--admit_smt_queries true' ./everest -j $EVEREST_THREADS hacl-star make
ENV FSTAR_HOME $HOME/everest/FStar
ENV KREMLIN_HOME $HOME/everest/kremlin
ENV QD_HOME $HOME/everest/quackyducky
ENV HACL_HOME $HOME/everest/hacl-star
ENV MLCRYPTO_HOME $HOME/everest/MLCrypto
RUN ./everest -j $EVEREST_THREADS MLCrypto make
ENV VALE_HOME $HOME/everest/vale
RUN echo export PATH=$HOME/everest/z3/bin:$PATH | tee --append .bash_profile .profile .bashrc
RUN env OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2)) -C hacl-star vale-fst
RUN env OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2)) -C hacl-star compile-evercrypt-external-headers
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

