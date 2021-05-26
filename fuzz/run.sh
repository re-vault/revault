# Fetch the corpus from https://github.com/revault/revault_tx_corpus and run the targets on it
# Meant to be ran by CI
#!/usr/bin/env sh

cd corpus && git clone https://github.com/revault/revault_tx_corpus

cargo install --force cargo-fuzz
for target in $(ls fuzz/fuzz_targets);do
    cargo +nightly fuzz run -O -a "${target%.*}" -- -runs=0 -maxlen=500000
done
