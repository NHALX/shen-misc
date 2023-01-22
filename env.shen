
(datatype ctx
             (dynamic (env | P)), F : Sig >> (shen.intro F Rules) : A;
    ___________________________________________________________________________

                 F : (context P Sig) >> (shen.intro F Rules) : A;


      ______________________________________________________________________
         (dynamic (env | P)), F : (context P (A --> B)) >> F : (A --> B);


                                Rules : (A --> B);
                  ______________________________________________
                    F : (A --> B) >> (shen.intro F Rules) : C;)


(load "misc.shen")

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
  Env Stack Value -> (let References (references Stack Value)
                          Assoc      (foldl (/. B A [(@p A (gensym (protect Var))) | B]) References [])
                          Value*     (substitute Assoc Value)

                        (foldl (/. B A [let (snd A) [fluid-value (fst A)] B])
                               Assoc
                               Value*)))

(define env-let-macro-h
  Env Stack [Symbol Value | XS] -> (let Stack [Symbol | Stack]
                                        Value (env-let-bind Env Stack Value)
                                      [fluid-let Symbol Value
                                                 [freeze (env-let-macro-h Env Stack XS)]])

  Env Stack [Expr] -> (env-let-bind Env Stack Expr))

\\ TODO: this macro doesn't deal with lambda binders correctly or direct calls to fluid-let/fluid-value
(defmacro env-let-macro
  [let! | XS] -> (env-let-macro-h [value *fluid-global*] [] XS))

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

(datatype @env-freeze@

                  (dynamic (env | New)) >> X : A;
          _______________________________________________
    (dynamic (env | _)) >> (freeze X) : (context New (lazy A));

                  (dynamic (env | New)) >> X : A;
          _______________________________________________
               (freeze X) : (context New (lazy A));

                   X : (context Want (lazy A));
                      (check-all Want Have);
          _______________________________________________
            (dynamic (env | Have)) >> (inject X) : A;)


(datatype @env-let@

                         (update Key r A Have Have*);
                     (dynamic (env | Have*)) >> Body : C;
                _____________________________________________
                  (- (let-body Have Key A C (freeze Body)));


                                      !;
                          (dynamic (env | Have)) >> Value : A;
                        (let-body Have Key A C Body);
    ______________________________________________________________________
               (dynamic (env | Have)) >> (fluid-let Key Value Body) : C;

                                  Value : A;
                         (let-body () Key A C Body);
    ______________________________________________________________________
                       (fluid-let Key Value Body) : C;


                           (env? Key r A Have);
      _________________________________________________________________
                    (dynamic (env | Have)) >> (fluid-value Key) : A;

                                      )






(datatype @env@


           let Query (fl-query Key Domain Set)
               (unify (just Type) Query);
     \\            (contains? Key Domain Type Set);
        _________________________________________
              (env? Key Domain Type Set);

                    (check-all B A);
    _________________________________________________
           X : (dynamic (env | A)) >> X : (dynamic (env | B));

                            )

\*

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
*\






(set *fluid-global* (vector 4096))

(define inject
  X -> (thaw X))

(define fluid-let
  X Y K -> (let NS (value *fluid-global*)
                Stack (trap-error (get X r NS) (/. Error []))
              (trap-error (do (put X r [Y|Stack] NS)
                              (let Ret (thaw K)
                                 (do (put X r Stack NS)
                                     Ret)))
                          (/. E (do
                                 (put X r Stack NS)
                                 (simple-error E))))))

(define fluid-value
  X -> (head (get X r (value *fluid-global*))))

\*
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
*\

(tc +)

\\\\\\\\\\\\\ tests
\*
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

(lambda E (let E (type E (env *key1* : r A
                              *key2* : r B))

             (@p (fluid-value E *key1*)
                 (fluid-value E *key2*))))
*\

(define test3
  { (context (*test2* : r number) (lazy number)) --> number }

  X -> (let!
           *test* 1
           *test2* (+ 1 *test*)
         (inject X)) )


(define test4
  { context (*test2* : r number) (number --> number) }

  N -> (+ N (fluid-value *test2*)) )

(let! *test* 1 *test*)

(fluid-let *test* 1
           (freeze (fluid-value *test*)))


(fluid-let *test2* 10
           (freeze (test4 1)))


(let X (type (freeze (fluid-value *test2*))
             (context (*test2* : r number) (lazy number)))

   (fluid-let *test2* 0
              (freeze (test3 X))))


(let X (type (freeze (fluid-value *test2*))
             (context (*test2* : r string) (lazy string)))

   (fluid-let *test2* 0
              (freeze (test3 X))))
