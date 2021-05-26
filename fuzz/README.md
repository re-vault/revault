To run against the current corpus, from the root of the repository:
```
[ -d ../tx_corpus ] || git clone https://github.com/revault/revault_tx_corpus ../tx_corpus
for target in $(ls fuzz/fuzz_targets); do cargo +nightly fuzz run --release --all-features --debug-assertions --sanitizer none "${target%.*}" -- -runs=0 -maxlen=500000 ../tx_corpus; done
```
