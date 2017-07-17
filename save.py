(define (analyze expr)
  (cond ((atom? expr) expr)
        ((quoted? expr)expr)
        ((or (lambda? expr)
             (define? expr))
         (let ((form   (car expr))
               (params (cadr expr))
               (body   (cddr expr)))
           'YOUR-CODE-HERE3
           (cons form (cons params (apply-to-all analyze body) ))))
        ((let? expr)
         (let ((values (cadr expr))
               (body   (cddr expr)))
           'YOUR-CODE-HERE1
            (cons (cons 'lambda values) body)))
        (else
         'YOUR-CODE-HERE2
         expr
         )))