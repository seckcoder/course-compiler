compiler-course
===============

Compiler Course

## To do:
* Write Grammars for intermediate languages

Notes for work:

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

Coding guidelines:
* No more than 80 columns per line.
