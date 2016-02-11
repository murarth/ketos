;;; Provides a few helper macros for testing facilities.

(export (assert assert-eq assert-not run-tests))

;; Panics with a nice error message if the condition is false.
(macro (assert pred)
  `(if (not ,pred)
     (panic ,(format "assertion `~s` failed" pred))))

;; Panics with a nice error message if the condition is true.
(macro (assert-not pred)
  `(if ,pred
     (panic ,(format "assertion `not ~s` failed" pred))))

;; Panics with a nice error message if the two arguments are not equal.
(macro (assert-eq a b)
  `(let ((assert-lhs ,a)
         (assert-rhs ,b))
     (if (/= assert-lhs assert-rhs)
       (panic (format ,(format "assertion `~s == ~s` failed; ~~s /= ~~s" a b)
                      assert-lhs assert-rhs)))))

;; Given a set of `(define (name) ...)` expressions, runs each test function.
(macro (run-tests :rest test-defs)
  `(do
     ,@test-defs

     (define (run-test name fn)
       (do
         (print "Running test ~25a ... " name)
         (fn)
         (println "ok")))

     ,@(map-into ()
        (lambda (def)
          (let ((name (first (second def))))
            `(run-test ',name ,name)))
        test-defs)))

; We can't depend on the list module, so we duplicate this definition here.
(define (map-into out fn li)
  (if (null li)
    out
    (map-into (append out (fn (first li))) fn (tail li))))
