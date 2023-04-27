# Use Arch Linux base image
FROM archlinux:latest

# Install required dependencies
RUN pacman -Syu --noconfirm --needed base-devel git curl go rustup clang python binaryen

# Checkout namada fork
RUN git clone --branch rano/mbt/cubic-slashing --depth 1 https://github.com/informalsystems/namada

# Checkout tendermint fork
RUN git clone --branch v0.1.4-abciplus --depth 1 https://github.com/heliaxdev/tendermint

# Install Go and minimal Rust nightly
RUN rustup toolchain install nightly --profile minimal --target wasm32-unknown-unknown

# Setup tendermint
WORKDIR /tendermint
RUN make build

# Change working directory to namada
WORKDIR /namada

# Set environment variables
ENV TENDERMINT="/tendermint/build/tendermint" \
    RUSTUP_TOOLCHAIN=nightly \
    RUST_BACKTRACE=1 \
    NAMADA_E2E_KEEP_TEMP=true \
    NAMADA_E2E_DEBUG=true \
    NAMADA_E2E_USE_PREBUILT_BINARIES=true \
    NAMADA_E2E_EPOCH_DURATION=20

# Download MASP parameters
RUN curl --location --remote-name-all --create-dirs --output-dir /root/.masp-params \
    https://github.com/anoma/masp/raw/test_parameters/masp-{spend,output,convert}.params

# Build wasm
RUN make build-wasm-scripts

# Run cargo build
RUN cargo build && cargo build --tests

# Add cargo test command in bash history
RUN echo "cargo test mbt_tests -- --test-threads=1 --nocapture" > /root/.bash_history

# Default command
CMD ["/bin/bash"]
