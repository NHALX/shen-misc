(scm. "(optimize-level 3)")

(set *iterations* 1000000000)

(define repeat
  N Thunk -> N where (<= N 0)
  N Thunk -> (do (thaw Thunk)
                 (repeat (- N 1) Thunk)))


\* Benchmark 1: if/else with intermediate values let-bound  *\

(define benchmark-1
  Var1 Var2 Pass -> (if (cons? Var1)
                        (if (cons? Var2)
                            (let Var1/hd (hd Var1)
                               (if (= 2 Var1/hd)
                                   (let Var1/tl (tl Var1)
                                        Var2/hd (hd Var2)
                                      (if (= 2 Var2/hd)
                                          (let Var2/tl (tl Var2)
                                               B       Var1/tl
                                             (if (= B Var2/tl)
                                                 halt
                                                 Pass))
                                          Pass))
                                   Pass))
                            Pass)
                        Pass))



\* Benchmark 2: if/else no intermediate values bound *\

(define benchmark-2
  Var1 Var2 Pass -> (if (cons? Var1)
                        (if (cons? Var2)
                            (if (= 2 (hd Var1))
                                (if (= 2 (hd Var2))
                                    (let B (tl Var1)
                                       (if (= B (tl Var2))
                                           halt
                                           Pass))
                                    Pass)
                                Pass)
                            Pass)
                        Pass))




\* Benchmark 3: if/else with and merging *\

(define benchmark-3
  Var1 Var2 Pass -> (if (and (cons? Var1)
                             (cons? Var2)
                             (= 2 (hd Var1))
                             (= 2 (hd Var2))
                             (= (tl Var1)
                                (tl Var2)))

                        (let B (tl Var1)
                           halt)

                        Pass))



\* Benchmark 4: guard/freeze *\

(define guard
  Fail true Ok  -> (thaw Ok)
  Fail false Ok -> (Fail false))


(define benchmark-4
  Var1 Var2 Guard
    ->
(Guard (cons? Var1)
(freeze
(Guard (cons? Var2)
(freeze (let Var1/hd (hd Var1)
(Guard (= 2 Var1/hd)
(freeze (let Var1/tl (tl Var1)
        (let Var2/hd (hd Var2)
(Guard (= 2 Var2/hd)
(freeze (let Var2/tl (tl Var2)
        (let B Var1/tl
(Guard (= B Var2/tl)
       (freeze halt)))))))))))))))  )




\* Benchmark 5: CPS *\

(define k.hd
  X L R -> (if (cons? X)
               (R (hd X))
               (L false)))

(define k.tl
  X L R -> (if (cons? X)
               (R (tl X))
               (L false)))

(define k.guard
  true Fail Ok -> (Ok true)
  false Fail Ok -> (Fail false))


(define benchmark-5
  Var1 Var2 Pass ->
  (k.hd Var1             Pass (/. Var1/hd
  (k.guard (= 2 Var1/hd) Pass (/. _
  (k.tl Var1             Pass (/. Var1/tl
  (k.hd Var2             Pass (/. Var2/hd
  (k.guard (= 2 Var2/hd) Pass (/. _
  (k.tl Var2             Pass (/. Var2/tl
  (let B Var1/tl
  (k.guard (= B Var2/tl) Pass (/. _
  halt))))))))))))))))


\\ Benchmark 6: CPS local def

(scm.

 "(define (benchmark-6 V93398 V93399 V93400)

    (define
      (k.guard V93386 V93387 V93388)
      (if V93386
          (V93388 V93386)
          (V93387 V93386)))

    (define
      (k.tl V93357 V93358 V93359)
      (if (pair? V93357)
          (V93359 (cdr V93357))
          (V93358 #f)))


    (define
      (k.hd V93351 V93352 V93353)
      (if (pair? V93351)
          (V93353 (car V93351))
          (V93352 #f)))

    (k.hd V93398 V93400
             (lambda (Var1/hd)
               (k.guard (= 2 Var1/hd) V93400
                           (lambda (_)
                             (k.tl V93398 V93400 (lambda (Var1/tl)
                                                      (k.hd V93399 V93400
                                                               (lambda (Var2/hd)
                                                                 (k.guard (= 2 Var2/hd) V93400
                                                                             (lambda (_)
                                                                               (k.tl V93399 V93400
                                                                                                  (lambda (Var2/tl)
                                                                                                    ((lambda (B)
                                                                                                       (k.guard (= B Var2/tl) V93400
                                                                                                                   (lambda (_) (quote halt))))
                                                                                                     Var1/tl))))))))))))))")


\\ Run

(output "Benchmark 1~%")

(let
    Pass false
    Var1 (cons 2 1)
    Var2 (cons 2 1)

  (scm.time
   (repeat
    (value *iterations*)
    (freeze
     (benchmark-1 Var1 Var2 Pass)))))

(output "Benchmark 2~%")

(let
    Pass false
    Var1 (cons 2 1)
    Var2 (cons 2 1)
    _    (scm.collect 4 4)

  (scm.time
   (repeat
    (value *iterations*)
    (freeze
     (benchmark-2 Var1 Var2 Pass)))))

(output "Benchmark 3~%")

(let
    Pass false
    Var1 (cons 2 1)
    Var2 (cons 2 1)
    _    (scm.collect 4 4)

  (scm.time
   (repeat
    (value *iterations*)
    (freeze
     (benchmark-3 Var1 Var2 Pass)))))

(output "Benchmark 4~%")

(let Guard (guard (lambda X X))
     Var1 (cons 2 1)
     Var2 (cons 2 1)
     _    (scm.collect 4 4)

   (scm.time
    (repeat (value *iterations*)
            (freeze (benchmark-4 Var1 Var2 Guard)))))


(output "Benchmark 5~%")

(let Var1 (cons 2 1)
     Var2 (cons 2 1)
     Pass (/. X X)
     _    (scm.collect 4 4)

   (scm.time
    (repeat
     (value *iterations*)
     (freeze
      (benchmark-5 Var1 Var2 Pass)))))



(output "Benchmark 6~%")

(let Var1 (cons 2 1)
     Var2 (cons 2 1)
     Pass (/. X X)
     _    (scm.collect 4 4)

   (scm.time
    (repeat
     (value *iterations*)
     (freeze
      (scm.benchmark-6 Var1 Var2 Pass)))))
