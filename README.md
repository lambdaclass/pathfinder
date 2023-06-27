# Welcome

How to re-execute transactions with Starknet in Rust and the cairo-vm version using lambdaworks.

The script is still hacky, it needs a refactor:
```bash
#!/usr/bin/env bash
# Debian script
set -ex

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source "$HOME/.cargo/env"
rustup override set stable

sudo apt update -y
sudo apt install -y zstd git gcc pkg-config libssl-dev

git clone https://github.com/lambdaclass/pathfinder.git --branch starknet-in-rust-test
git clone git clone https://github.com/lambdaclass/starknet_in_rust.git --branch pathfinder-test
cd pathfinder

# 109G compressed
wget https://pub-1fac64c3c0334cda85b45bcc02635c32.r2.dev/mainnet_83389.sqlite.zst
# 210G uncompressed
zstd -d mainnet_83389.sqlite.zst
mv mainnet_83389.sqlite.zst mainnet.sqlite

# Run 10 blocks
cargo run --release -p pathfinder --example re_execute ./mainnet.sqlite 68000 68100```
