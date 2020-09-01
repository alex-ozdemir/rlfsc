# Rust implementation of LFSC

## Installation Instructions

1. Install the (nightly) Rust toolchain using [Rustup](https://rustup.rs/).
   * Be sure to add Cargo's bin directory to your path
      * i.e. by adding `export PATH="$HOME/.cargo/bin/:$PATH"` to your rc
         file.
2. Run `cargo install rlfsc`

## Possible improvements over the original LFSC

* Tokenizer and checker are separate.
* Tokenizer is **not** character-by-character
   * It's implemented using the `logos` library.
* Automatically reference-counted expressions using `std::rc::Rc`.
* No gotos/crazy stuff

## State of Affairs

On our small test proof (`pf`), we're ~30% slower than LFSC (10.8ms vs 8.0ms)
on my machine.

On the CVC4 signatures (`sig`), we're ~30% faster than LFSC (3.0ms vs 4.4ms)
on my machine.

This suggests that our tokenization is indeed better, but our checking is
slower.

We do lots of recursion, without tail recursion, causing us to blow small
stacks.

## Type checking algorithm

It's based on to Aaron's 2008 manuscript, "Proof Checking Technology for
Satisfiability Modulo Theories", but, in general, has no optimizations.

Notably:

* We always construct an AST for checked terms.
* In-scope identifiers are kept in a global map
* When an abstraction expression is instantiated, we substitute the provide
   value
   * e.g. `(\x t) v` becomes `t[v / x]`, literally. I.e. we take `t` apart,
      looking for all the `x`'s, replace them with `v`'s, and rebuild `t`.
* In code expressions, we do not do this.
   * e.g., when we evaluate `(let x v t)`, we put `x -> v` in the environment,
      and evaluate `t`, rather than substituting.

## Todos

* Tail Recursion
   * C historically has had poor support for tail recursion, which is why the
      original LFSC manually implemented it with gotos.
   * We can't (and won't) do that in Rust.
   * We should implement a trampoline-based approach
* Term destruction
   * When destructing terms (auto-implemented), we go into deep recursion.
   * We should manually implement some destructors to prevent this.
* Implement a streaming tokenizer.
   * Right now we need to bring the whole input into memory before tokenizing.
   * Option 1: Modify `logos` to allow this by implementing `logos::Source`
      for `std::io::Read`.
      * Doesn't quite work. We'll need to modify the requirements of `Source`
         a bit.
   * Option 2: Switch to a different tokenizing library.
      * Perhaps `nom`? It's typically used for parsing, but it does support
         streaming.
   * Option 3: Roll our own.
      * I think this is a bad idea. If [this blog
         post](https://blog.burntsushi.net/ripgrep/) taught me anything, it's
         that high-performance text processing is more complex than most
         people think. I think it would be very hard to match the perf of
         a dedicated library like `logos` or `nom`.
