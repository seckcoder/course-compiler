compiler-course
===============

Compiler Course

## To do:
* Implement anonymous functions: `lambda.rkt`
* Do: Look through S3 tests and think of more tests.
* Read: `functions.rkt` for help with `lambda.rkt`

Notes for work:

* Closure implementation is already handled for `define` bodies (*piggy back?*)
* What happens after type-checking? *Terms retain their types?*
* Does `e` in `(e e* ...)` have to be an abstraction?
* We have implicit `begin` expressions in abstraction bodies?
(i.e., `(e e* ...)` in the BNF)
* What is the signature of the list-members in `X-passes`? 

## Course Notes (thus far):
* Passes are contained within *projects*, for a few weeks
* All projects take input -> x86_64
* Every pass is a method building on an *object*; for **open recursion**
* Every project (Sx) requires only the previous (S(x - 1)). 

## Useful files:
* Look in utilities for System V
* Look in utilities for Debugging stuff (`check-passes`)

