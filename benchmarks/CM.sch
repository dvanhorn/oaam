#;#;
(define (UserFn sys) (sys UserFn))
(define (SystemFn user) (user SystemFn))
(define (RAUserFn sys)
  (frame (A) (sys RAUserFn)))
(define (RSSystemFn user)
  (frame (S) (user RSSystemFn)))

(RAUserFn RSSystemFn)