;; A very simple test to trigger allocation and deletion of vectors
;; use the test suite option --heap-size 1024 and this test should
;; easily cause an collection.
;; Conservative estimate:
;; 50 words per vector * 8 bytes per word * 3 vectors = 1200 bytes 
(let ([v0 (vector 42 ;;1 42 3 4;; 5 6 7 8 9
                  ;;10 11 12 13 14 15 16 17 18 19
                  ;;20 21 22 23 24 25 26 27 28 29
                  ;;30 31 32 33 34 35 36 37 38 39
                  ;;40 41 42 43 44 45 46 47 48 49
                  )])
  (vector-ref v0 0))

