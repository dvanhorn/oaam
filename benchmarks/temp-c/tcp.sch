(define TCPSocket? number?)
(define (TCPData? x)
  (or (eq? x 'SYN)
      (eq? x 'ACK)
      (eq? x 'SYN&ACK)
      (eq? x 'FIN)
      (and (pair? x)
           (eq? (car x) 'Data))))

(define (tcp-open socket)
  (cons (λ (data) (void)) ;; dummy send
        (cons (λ () (let ([dummy (random)]) (if (TCPData? dummy) dummy (error 'hodor?)))) ;; dummy recv
         (cons (λ (duration) (void)) ;; dummy timeout
               (λ () (void)))))) ;; dummy close

(define (tcp-listen socket)
  (cons (λ (data) (void))
        (cons (λ () (let ([dummy (random)]) (if (TCPData? dummy) dummy (error 'hodor!))))
         (cons (λ (duration) (void))
               (λ () (void))))))

(define ctcp-open
  (tmon 'sender 'context 'contract
        (->
         TCPSocket?
         (cons/c
          ('send : TCPData? : -> void?)
          (cons/c ('recv : -> TCPData?)
                  (cons/c ('timeout : number? -> void?)
                          ('close : -> void?)))))
        (· (call (label send) 'SYN)
           (!call (label close))
           (ret (label recv) 'SYN&ACK)
           (!call (label close))
           (call (label send) 'ACK)
           (* (!call (label close)))
           (∪ (· (ret (label recv) 'FIN) (call (label send) 'ACK) (call (label send) 'FIN) (ret (label recv) 'ACK))
              (· (call (label close)) (call (label send) 'FIN) (ret (label recv) 'ACK) (ret (label recv) 'FIN) (call (label send) 'ACK)))
           (ret (label timeout) _) (ret (label close) _))
        tcp-open))

(define ctcp-listen
 (tmon 'listener 'context 'contract
       (-> TCPSocket?
           (cons/c
            ('send : TCPData? : -> void?)
            (cons/c ('recv : -> TCPData?)
                    (cons/c ('timeout : number? -> void?)
                            ('close : -> void?)))))
       (· (ret (label recv) 'SYN)
          (!call (label close))
          (call (label send) 'SYN&ACK)
          (!call (label close))
          (ret (label recv) 'ACK)
          (* (!call (label close)))
          (∪ (· (call (label close)) (call (label send) 'FIN) (ret (label recv) 'ACK) (ret (label recv) 'FIN) (call (label send) 'ACK))
             (· (ret (label recv) 'FIN) (call (label send) 'ACK) (call (label close)) (call (label send) 'FIN) (ret (label recv) ACK)))
          (ret (label timeout) _)
          (ret (label close) _))
       tcp-listen))