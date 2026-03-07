FROM ubuntu:22.04

RUN apt-get update && apt-get install -y \
    curl \
    gcc \
    m4 \
    git \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
    sh -s -- --default-toolchain nightly -y --no-modify-path

ENV PATH="$PATH:/root/.cargo/bin"

CMD cd /app && cargo test

