# Student Test Suite

### R1
* (1-4) Tests for basic arithmetic and flattening
* (5-6) Tests for Uniquify
* (7-8) Flattening tests for `let`
* (9-10) `(read)` functionality
* (11-12) Extreme flatten tests
* (13) Stack-stack binop variable
* (14) Variable name reuse/scoping
* (15) Let with binop in binding
* (16) Lets under binop
* (17) Stack-stack move variable
* (18) Uniquifying, use of correct variable

Register allocation -r1a
* 1 - force spillage
* 2 - movq special case for liveness analysis is correct
* 3 - varying & overlapping lifetimes
* 4 - force early spillage because of read
* 5 - lots of read
* 6 - lots of read, but unused variables
* 7 - spill, but then do "regular" work -- ensure that variables aren't given unique locations on the stack after spilling

### R2 (Coming soon)
