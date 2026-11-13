(module traffic base
  (require fsm)
  (define-fsm light (green (timer yellow)) (yellow (timer red)) (red (timer green) (fault flashing)))
  (define (run s evs) (if (null? evs) s (run (light s (car evs)) (cdr evs))))
  (provide run light))
