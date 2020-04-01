# coq-yul

A Coq implementation of Ethereum's [Yul](https://solidity.readthedocs.io/en/latest/yul.html).

This is an early release that only includes a bigstep, dynamically-typed semantics.


Notes:

- Reentrancy is not modelled. It's not practical to model it in bigstep.
- Functions and variables inhabit two independent namespaces.
  This is OK:

        function foo()
        {
            let foo := 0
        }

  The Yul doc doesn't make that clear.

- Some [restrictions](https://solidity.readthedocs.io/en/latest/yul.html#restrictions-on-the-grammar) are not implemented, most importantly:
  - If a variable is inaccessible, it's also considered invisible.
      This is OK:

        let x := 0
        function foo()
        {
            let x := 0  // the outer x is inaccessible here
        }

      The YUL doc forbids this by introducing a somewhat weird notion of visible
      but inaccessible names. A special static check for this can be added later.
      
## Building

    coq_makefile -f _CoqProject -o Makefile
    make
    
Checked with Coq 8.11.