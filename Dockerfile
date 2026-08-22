FROM ubuntu:focal

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y curl vim git python3 python3-pip time opam wget
RUN apt-get update && apt-get install -y build-essential m4 pkg-config libgmp-dev\
                                        apt-utils libssl-dev zlib1g-dev bubblewrap\
                                        libpam0g-dev libaudit-dev liblz4-dev libzstd-dev\
                                        libssh2-1-dev libnghttp2-dev libpq-dev libmysqlclient-dev\
                                        libhiredis-dev libjson-c-dev libyajl-dev libwebp-dev\
                                        libavcodec-dev libavformat-dev libavutil-dev\
                                        libswscale-dev libsdl2-dev libgsl-dev libfftw3-dev\
                                        libuv1-dev libprotobuf-c-dev libcap-dev\
                                        libbz2-dev liblzma-dev libcurl4-openssl-dev libsqlite3-dev \
                                        libxml2-dev libpng-dev libjpeg-dev libtiff-dev libgif-dev \
                                        libicu-dev libreadline-dev libgtk-3-dev libcairo2-dev \
                                        libpango1.0-dev liblapack-dev libblas-dev libevent-dev

RUN wget -O - https://download.grammatech.com/gtirb/files/apt-repo/conf/apt.gpg.key | apt-key add -
RUN echo "deb https://download.grammatech.com/gtirb/files/apt-repo focal stable"| tee -a /etc/apt/sources.list
RUN apt-get update
RUN apt-get install -y gtirb-pprinter ddisasm

RUN bash -c "$(curl -fsSL https://raw.githubusercontent.com/ohmybash/oh-my-bash/master/tools/install.sh)"
RUN export OPAMCONFIRMLEVEL=unsafe-yes
RUN opam init --disable-sandboxing --yes
RUN eval $(opam env)
RUN opam update
RUN opam switch create 4.14.0
RUN opam switch 4.14.0
RUN opam install coq.8.20.0 menhir yojson --yes
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
RUN echo 'source $HOME/.cargo/env' >> $HOME/.bashrc
RUN . "$HOME/.cargo/env"
RUN echo 'eval $(opam env)' >> ~/.bashrc

