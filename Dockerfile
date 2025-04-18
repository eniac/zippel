# Indicate the Gurobi reference image
FROM gurobi/optimizer:latest

RUN apt-get update && apt-get install -y \
    curl \
    gcc \
    gpg \
    m4 \
    pkg-config \
    python3 \
    python3-pip \
    python3-setuptools \
    python3-dev \
    && rm -rf /var/lib/apt/lists/*

# Install rustup (if not already installed) and set the default toolchain to nightly
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
    sh -s -- --default-toolchain nightly -y --no-modify-path

ENV PATH="$PATH:/root/.cargo/bin"

CMD  cd /app && \
     gpg --quiet --batch --yes --decrypt --passphrase=$GUROBI_KEY \
         --output /opt/gurobi/gurobi.lic gurobi.lic.gpg && \
     cargo test

