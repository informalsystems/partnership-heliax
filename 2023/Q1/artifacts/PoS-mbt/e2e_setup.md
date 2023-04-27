# Namada Blockchain E2E Test Setup

This guide will walk you through the process of setting up and running the
namada blockchain end-to-end (e2e) test.

## Prerequisites

Before we proceed with the setup, make sure you have Rust `nightly` installed
with `wasm32`:

```sh
rustup toolchain install nightly --target wasm32-unknown-unknown
```

## Clone Repositories

Now, clone the `namada` and `tendermint` repositories:

```sh
git clone --branch rano/mbt/cubic-slashing --depth 1 https://github.com/informalsystems/namada
git clone --branch v0.1.4-abciplus --depth 1 https://github.com/heliaxdev/tendermint
```

## Build Tendermint

Navigate to the tendermint directory, build it and set it on environment
variable:

```sh
cd tendermint
make build
```

## Download MASP Parameters

Download the MASP parameters:

```sh
curl --location --remote-name-all --create-dirs --output-dir ~/.masp-params \
    https://github.com/anoma/masp/raw/test_parameters/masp-{spend,output,convert}.params
```

## Prepare for each test

### Change to the Namada Directory

```sh
cd namada
```

### Set the `TENDERMINT` Environment Variable

```sh
export TENDERMINT="${TENDERMINT_ROOT_DIR}/build/tendermint"
```

### Build Namada

Navigate to the namada directory and build wasm scripts and namada binaries:

```sh
RUSTUP_TOOLCHAIN=nightly make build-wasm-scripts
cargo +nightly build
```

## Run the E2E Test

You're now ready to run the e2e test:

```sh
RUST_BACKTRACE=1 NAMADA_E2E_KEEP_TEMP=true NAMADA_E2E_DEBUG=true NAMADA_E2E_USE_PREBUILT_BINARIES=true NAMADA_E2E_EPOCH_DURATION=20 cargo +nightly test mbt_tests -- --test-threads=1 --nocapture
```
