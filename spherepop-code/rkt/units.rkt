(module units base
  (define (c->f c) (+ 32 (/ (* c 9) 5)))
  (define (km->miles k) (/ (* k 621371) 1000000))
  (define (internal-helper x) (* x 1000))
  (provide c->f km->miles))
