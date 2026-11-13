(module fsm base
  (define-syntax-rule (define-fsm name (state (event next) ...) ...)
    (define (name st ev)
      (cond ((eq? st 'state) (cond ((eq? ev 'event) 'next) ... (else 'error))) ...
            (else 'error))))
  (provide define-fsm))
