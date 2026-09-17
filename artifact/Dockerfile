# Zippel IEEE S&P 2027 artifact-evaluation image.
#
# Build from the repository root (not from artifact/), so the build
# context includes the whole workspace. UID/GID must match the host user
# (see below), so build with:
#
#   docker build -f artifact/Dockerfile -t zippel-ae \
#     --build-arg UID=$(id -u) --build-arg GID=$(id -g) .
#
# Run with a shell to explore, or invoke one of artifact/scripts/*.sh
# directly:
#
#   docker run --rm -it zippel-ae
#   docker run --rm zippel-ae artifact/scripts/smoke_test.sh

# Same base image as .github/workflows/ci.yml's `test` job. The exact
# nightly toolchain comes from rust-toolchain.toml (fetched automatically
# by rustup on first cargo invocation below), not from this image tag.
FROM rustlang/rust:nightly

# Matches ci.yml's `test` job build deps exactly (gcc/m4/pkg-config for
# the arkworks/GMP dependency chain, singular for the Groebner-basis
# backend used by the completeness/soundness analyses).
RUN apt-get update && \
    apt-get install -y --no-install-recommends gcc m4 pkg-config singular && \
    rm -rf /var/lib/apt/lists/*

# Build and run as a non-root user matching the host UID/GID, so files
# written to /zippel/target and to a bind-mounted artifact/output/ aren't
# left owned by root. No default: a guessed one (e.g. "1000") could
# silently mismatch the host and produce wrong ownership instead of a
# build failure.
ARG UID
ARG GID
RUN if [ -z "${UID}" ] || [ -z "${GID}" ]; then \
      echo "ERROR: build with --build-arg UID=\$(id -u) --build-arg GID=\$(id -g) so the image's user matches yours. Refusing to guess a default." >&2; \
      exit 1; \
    fi
RUN groupadd -o -g "${GID}" zippel && \
    useradd -o -m -u "${UID}" -g "${GID}" -s /bin/bash zippel && \
    chown -R "${UID}:${GID}" /usr/local/cargo /usr/local/rustup

COPY --chown=${UID}:${GID} . /zippel
WORKDIR /zippel

USER zippel

# Resolves rust-toolchain.toml's pinned nightly and prebuilds the full
# workspace (including the benchmarks crate, a workspace member but not a
# default-member). `--all-targets` is required for this to touch what the
# scripts run at all: plain `cargo build` only builds lib/bin targets, not
# the examples, test harnesses (e.g. `gb_snapshots`), or benches (`inline`,
# `inline_all`) that the three experiments and smoke_test.sh actually
# invoke. This does NOT eliminate compile time on every `docker run`
# though: `cargo test -p <crate>` and `cargo bench` each still trigger
# their own partial recompile the first time that specific command runs
# in a container, even with this prebuild in place (see artifact/README.md's
# "Note on recompiles").
RUN cargo build --workspace --release --all-targets

CMD ["/bin/bash"]
