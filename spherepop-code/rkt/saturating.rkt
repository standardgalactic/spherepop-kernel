(module saturating base
  (require (prefix-in b: (only-in base +)))
  (define (+ a c) (let ((s (b:+ a c))) (if (> s 100) 100 s)))
  (provide + (all-from-out base)))
