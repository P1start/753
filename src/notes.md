Implementation notes
====================

Compile-time evaluation
-----------------------

Full compile-time evaluation is a tricky thing to do. This is because it
makes the compilation process highly non-linear. For example, compile-time
code can both use functions defined elsewhere and define its own functions.
As a result, sometimes functions will have to be compiled and run before some
other functions are even known to exist!

The plan:

1.  Create a list of every function, type, static variable etc. (henceforth
    'symbol') defined in the global namespace.
2.  Figure out which symbols refer to undefined symbols and mark them
    excluded, and also transitively mark any symbols which refer to them as
    excluded, and so on.
3.  Compile all leftover symbols.
4.  Compile and run the first macro that depends only on compiled symbols.
    Here 'macro' simply refers to any kind of thing that runs code at compile
    time.
5.  Repeat steps 2–4 until all macros have been executed. If any symbols
    refer to undefined symbols now, throw an error.

The key point here to start with is that we need the compiler to work on the
level of single declarations/symbols and not a whole file.