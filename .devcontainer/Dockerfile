# Use the C++ dev container as a base
FROM mcr.microsoft.com/devcontainers/cpp:latest

# Set a non-interactive shell to avoid prompts
ARG DEBIAN_FRONTEND=noninteractive

# Install Python, pip, and venv
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 \
    python3-pip \
    python3-venv

# Create and activate virtual environment
ENV VENV_PATH=/opt/venv
RUN python3 -m venv $VENV_PATH
ENV PATH="$VENV_PATH/bin:$PATH"

# Install Python packages (openai)
RUN pip3 install openai

# Additional package installation and setup
RUN apt-get install -y wget byacc flex autoconf automake libtool-bin libtool g++ libgtest-dev mercurial libboost-all-dev
WORKDIR /usr/src/spin
RUN wget https://github.com/nimble-code/Spin/archive/refs/tags/version-6.5.2.tar.gz && \
    tar -xvf version-6.5.2.tar.gz && \
    rm version-6.5.2.tar.gz
WORKDIR /usr/src/spin/Spin-version-6.5.2/Src
RUN make
RUN cp spin /usr/local/bin

# Clean up to reduce image size
RUN apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*


# Install Texada
# compile and setup google test:

# WORKDIR /usr/src
# RUN git clone https://code.google.com/p/googletest
# RUN mv googletest gtest

# WORKDIR /usr/src/gtest
# RUN cmake CMakeLists.txt
# RUN make
# RUN cp *.a /usr/lib

# install spot:
# WORKDIR /usr/src/spot
# RUN wget https://www.lrde.epita.fr/dload/spot/spot-1.2.5.tar.gz 
# RUN tar -xvf spot-1.2.5.tar.gz

# # WORKDIR /usr/src/spot/spot-1.2.5
# # RUN ./configure
# # RUN make
# # RUN make check
# # RUN make install

# # # grab texada:
# WORKDIR /usr/src
# RUN git clone https://github.com/ModelInference/texada.git
# WORKDIR /usr/src/texada

# RUN export TEXADA_HOME=$HOME/texada

# # set up the uservars.mk file based on the example that's there:
# RUN cp uservars.mk.example uservars.mk

# # only change the SPOT_INCL location since all other location
# # vars are available system-wide and need not be changed:
# RUN sed -i "/^SPOT_INCL:=/c\SPOT_INCL:=${PWD%/*}/spot-1.2.5/src/" uservars.mk

# # build texada and texadatest
# RUN make

# # run texadatest to make sure all the tests pass
# RUN ./texadatest



# Set the default work directory
WORKDIR /workspace
