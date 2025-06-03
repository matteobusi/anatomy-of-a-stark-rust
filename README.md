# Anatomy of a STARK, in Rust

I am currently learning both Rust and STARKs.
Why not combine these two interests by re-implementing of the [Anatomy of a STARK tutorial](https://aszepieniec.github.io/stark-anatomy/) in Rust as I go through it?

The project is organized in modules and is lightly documented, with occasional comments complementing the contents of the original tutorial. The idea is to have a simple enough implementation of a STARK that I can fully understand and hopefully formalize and analyze in [Rocq](https://rocq-prover.org/) using [StrandsRocq](https://github.com/strandsrocq/strandsrocq).

# A word about crypto-bigint

I included the source code of the [crypto-bigint](https://github.com/RustCrypto/crypto-bigint/) library which I minimally extended to support [`adt_const_params`](https://doc.rust-lang.org/beta/unstable-book/language-features/adt-const-params.html) which are an unstable feature of Rust that supports `const` generics for non-native types. This allows my `finite_fields` library to include the prime and the generator (which are 256-bit big integers) in the type itself, so moving some runtime checks to compile time.

# 🚧 This is a work in progress 🚧
This code is *not* ready for production. I'm aiming for clarity and correctness, but the implementation probably contains bugs :)

## TODOs
1. Property-based testing
2.

# License

I am including the [crypto-bigint](https://github.com/RustCrypto/crypto-bigint/) code, for their license please refer to the relevant files in their folder.

All the other code I wrote is released under the [MIT license](http://opensource.org/licenses/MIT).
