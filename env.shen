
(define references
  Stack [L|R] -> (union (references Stack L)
                        (references Stack R))
  Stack Y -> [Y]
    where (element? Y Stack)

  Stack _ -> [])


(define substitute
  Assoc [L|R] -> [(substitute Assoc L) | (substitute Assoc R)]
  Assoc X     -> (let Var (alist.value X Assoc)
                    (if (!? Var) Var X))
    where (symbol? X)
  Assoc X     -> X)

(define env-let-bind
  Env Stack Value K -> (let References (references Stack Value)
                              Assoc      (foldl (/. B A [(@p A (gensym (protect Var))) | B]) References [])
                              Value*     (substitute Assoc Value)

                            (foldl (/. B A [let (snd A) [fluid-value Env (fst A)] B])
                                   Assoc
                                   (K Value*)) ) )

(define env-let-macro-h
  Env Stack [Symbol Value | XS] -> (let Stack [Symbol | Stack]
                                        (env-let-bind Env Stack Value
                                                        (/. X [fluid-let Env Symbol X
                                                                         [freeze (env-let-macro-h Env Stack XS)]])))

  Env Stack [Expr] -> (env-let-bind Env Stack Expr (/. Expr* Expr*)))

\\ TODO: this macro doesn't deal with lambda binders correctly or direct calls to fluid-let/fluid-value
(defmacro env-let-macro
  [let! Env | XS] -> (env-let-macro-h Env [] XS)
    where (variable? Env))

\*
(macroexpand
 [let! Env
     *test* [+ 1 *test*]
     *var* [+ *var* *test*]
     [/ *var* *test*]])
*\


(define fl-query
  Key Domain [Key : Domain Value | XS] -> [just Value]
  Key Domain [_ : _ _ | XS] -> (fl-query Key Domain XS)
  _ _ _ -> nothing)



(datatype @env-update@

               if (and (== Key K) (== Domain D))
                              !;
            (unify (Key : Domain Value | XS) Tail);
    _______________________________________________________
      (- (update Key Domain Value (K : D _ | XS) Tail));

               (update Key Domain Value XS XS*);
                 (unify (K : D V | XS*) Tail);
       _________________________________________________
      (- (update Key Domain Value (K : D V | XS) Tail));

                              !;
              (unify (Key : Domain Value) Tail);
       _________________________________________________
            (- (update Key Domain Value () Tail));

                               )

(datatype @env-find@

              if (and (== Key K) (== Domain D))
                         let Tail XS
                       (unify Value V);
                              !;
      _________________________________________________
       (- (find Key Domain Value (K : D V | XS) Tail));

               (find Key Domain Value XS Tail);
    ______________________________________________________
       (- (find Key Domain Value (_ : _ _ | XS) Tail));

                              )

(datatype @env-check-all@
                            !;
    ___________________________________________________
                (- (check-all () Context));

                 let Something (gensym &&)
              (find K D V2 Context Context*);
             Something : V >> Something : V2;
                 (check-all XS Context*);
    ___________________________________________________
          (- (check-all (K : D V | XS) Context));

                             )

(datatype @env-let@
                          \\\\\\\\\\\\\\\\\\\\\\\\\\\\

                     Env : (env | Have) >> Value : A;
                       (update Key r A Have Have*);
                 Env : (env | Have*) >> Body : (lazy C);
                   \\  (check-all Want (Key : A | Have*));
    ______________________________________________________________________
       Env : (env | Have) >> (fluid-let Env Key Value Body) : C;

                           (env? Key r A Have);
      _________________________________________________________________
             Env : (env | Have) >> (fluid-value Env Key) : A;

                                      )


(datatype @env-reap@
                           \\\\\\\\\\\\\\\\\\\\\\\\

                        (update Key w W Have Have*);
                 Env : (env | Have*) >> Body : (lazy C);
    ________________________________________________________________________
      Env : (env | Have) >> (reap Env Key Body) : ((list W) * C);


                      Env : (env | Have) >> Value : A;
                           (env? Key w A Have);
      _________________________________________________________________
              Env : (env | Have) >> (sow Env Key Value) : A;

                                       )


(datatype @env-state@
                           \\\\\\\\\\\\\\\\\\\\\\\\

                         Env : (env | Have) >> Value : A;
                            (update Key rw A Have Have*);
                     Env : (env | Have*) >> Body : (lazy C);
    ______________________________________________________________________________
           Env : (env | Have) >> (state-init Env Key Value Body) : C;


                           (env? Key rw A Have);
      _________________________________________________________________
             Env : (env | Have) >> (state-value Env Key) : A;

                                   Value : A;
                           (env? Key rw A Have);
      _________________________________________________________________
          Env : (env | Have) >> (state-set Env Key Value) : A;


                                       )

(datatype @env@


           let Query (fl-query Key Domain Set)
               (unify (just Type) Query);
        _________________________________________
              (env? Key Domain Type Set);

            ________________________________
                 (env-new) : (env);

                    (check-all B A);
    _________________________________________________
           X : (env | A) >> X : (env | B);

                            )







(define fluid-let
  NS X Y K -> (let Stack (trap-error (get X r NS) (/. Error []))
                 (trap-error (do (put X r [Y|Stack] NS)
                                 (let Ret (thaw K)
                                    (do (put X r Stack NS)
                                        Ret)))
                             (/. E (do
                                    (put X r Stack NS)
                                    (simple-error E))))))

(define fluid-value
  NS X -> (head (get X r NS)))

(define state-value
  NS X -> (get X rw NS))

(define state-set
  NS X Y -> (put X rw Y NS))

(define state-init
  NS X Y K -> (do (put X rw Y NS)
                  (thaw K)))

(define sow
  NS X Y -> (put X w (cons Y (get X w NS)) NS))

(define reap
  NS X K -> (let Old (trap-error (get X w NS) (/. Error []))
               (trap-error (do (put X w [] NS)
                               (let Ret (thaw K)
                                    Log (get X w NS)
                                  (do (put X w Old NS)
                                      (@p Log Ret))))
                           (/. E (do
                                  (put X w Old NS)
                                  (simple-error E))))))

(define env-new
  -> (vector 128))



(tc +)

\\\\\\\\\\\\\ tests

(define test
  { (env) --> ((list number) * string) }

  Env -> (reap Env *key* (freeze (do
                                      (sow Env *key* 1)
                                      (sow Env *key* 1)
                                      "hi"))))


(test (env-new))


(define test2
  { (env) --> number }

  Env -> (state-init Env *key* 1
                       (freeze (let N (state-value Env *key*)
                                  (state-set Env *key* (+ 1 N))))))


(test2 (env-new))



(define test3
  { (env *test2* : r number) --> (lazy number) --> number }

  Env X -> (let! Env
               *test* 1
               *test2* (+ 1 *test*)
             (thaw X)))


(let Env (env-new)
   (fluid-let Env
              *test2* 0
              (freeze (test3 Env (freeze (fluid-value Env *test2* ))))))
