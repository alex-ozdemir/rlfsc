# Rust implementation of LFSC

## Run Instructions

* Increase the stack size: `ulimit -s $(( 2 ** 20))`
* `cargo run [--release] pf`.

## Possible improvements over the original LFSC

* Tokenizer and checker are separate.
* Tokenizer is **not** character-by-character
   * It's implemented using the `logos` library.
* Automatically reference-counted expressions using `std::rc::Rc`.


## State of Affairs

On our small test proof (`pf`), we're ~30% slower than LFSC (10.8ms vs 8.0ms)
on my machine.

On the CVC4 signatures (`sig`), we're ~30% faster than LFSC (3.0ms vs 4.4ms)
on my machine.

This suggests that our tokenization is indeed better, but our checking is
slower.

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
   * C historically has had poor support for tail recusion, which is why the
      original LFSC manually implemented it with gotos.
   * We can't (and won't) do that in Rust.
   * We could implement a loop-based tail recursion.
   * Perhaps it would be better to do a trampoline-based approach?
      * e.g. with `tramp`.
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
* Allow for construction-less checking.
   * Right now we always construct the checked term.
     We often don't need to.
   * This isn't hard to do, but it might be worth figuring out how to do it
      without duplicating too much code.
      * Idea: initialize a "result" option and map over it?
* Stop doing substitutions?
   * The original LFSC implementation represents bound variables as objects
      which (a) the binding and (b) the uses have pointers to. During
      instantiation, that variable gets pointed to its value.
   * Is this better?
   * This requires them to clone abstractions in order to instantiate them
      multiple times.
   * That seems just (nearly?) as base as substitution.
   * It might enable a single-use optimization.
      * Does this optimization work?
      * Does it help?
