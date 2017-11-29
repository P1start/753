753
===

753 is a compiled, statically-typed Lisp-like language.

Status
------

753 is not currently in a usable state. Everything is in a state of flux, including the name.

Design goals
------------

- Fast: aiming to rival C++
  - LLVM backend
- Lisp-like syntax
- Strong, static typing with function overloading
- Powerful macro system and compile-time evaluation

### Assorted ideas

- ‘Current objects’ (better name needed): see https://github.com/PistonDevelopers/dyon/issues/224.
  - In particular, I hope that these will be able to be used in lieu of traits/interfaces. Instead
    of requiring that a type parameter of a function implement a trait, instead we can make the
    necessary associated items (usually functions) ‘current objects’ for the function. This is
    superior to traits in two ways:
      - it doesn’t add any complexity to the type system and all the complications that traits
        imply;
      - a type can ‘implement’ the same ‘trait’ in more than one way, and the specific 
        implementation used is based on which current variable you use.
    Common ‘trait implementations’ would be implemented using global ‘current objects’ (if that
    makes any sense; more thought on this subject is needed).