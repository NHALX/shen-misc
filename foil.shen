(tc -) \\ untyped


\\ system patch

(package shen [&]

 (defprolog t*-integrity
   (- []) B _ B                      <--;
   (- [P | Ps]) (- [A --> B]) Hyps C <-- (system-S-h P A [integrity-check|Hyps])
                                         (t*-integrity Ps B Hyps C);)
 )

\\ untyped foil

(define cast
  X -> X)

(define foil-new
    -> (gensym &&))




(tc +) \\ typed



\\ option module

(datatype @verified@
                   P : verified >> X : T;
                           Y : T;
      ________________________________________________
                      (if P X Y) : T;


     _________________________________________________
                  X : A >> X : (- (? A));

                           X : A;
     _________________________________________________
                       X : (- (? A));

     _________________________________________________
           X : (? A), (!? X) : verified >> X : A;

    ____________________________________________________
                        ? : (? A);)


(define !?
  { A --> boolean }
  X -> (not (== ? X)))


\\ fake alist module

(synonyms (alist.alist K V) (list (K * V)))

(define alist.value
  { A --> (alist.alist A B) --> (? B) }
  A [] -> ?
  A [(@p A B)|XS] -> B
  A [_|XS] -> (alist.value A XS))

(define alist.set
  { A --> B --> (alist.alist A B) --> (alist.alist A B) }
  K V XS -> [(@p K V) | XS])





\\ foil module


(datatype @substitutions@
                                            !;
    __________________________________________________________________________________
           X : (- (substitutions A B)) >> X : (alist.alist (name A) (foil B));

    __________________________________________________________________________________
     X : (- (substitutions AS BS)) >> X : (alist.alist (name [A|AS]) (foil [B|BS]));


                           X : (alist.alist (name A) (foil B));
             _______________________________________________________________
                              X : (- (substitutions A B));)



(datatype @foil@
                           let U [X | (gensym &&)]
                              X : (name [U|N]);
                                Z : (foil N);
                              Y : (foil [U|N]);
           ________________________________________________________
                         [foil-let X Z Y] : (foil N);


                           let U [X | (gensym &&)]
                              X : (name [U|N]);
                              Y : (foil [U|N]);
           ________________________________________________________
                        [foil-lambda X Y] : (foil N);

                                 F : symbol;
                            XS : (list (foil N));
           ________________________________________________________
                       [foil-apply F | XS] : (foil N);

                                      !;
                                X : (name N);
    ______________________________________________________________________
               shen.integrity-check >> [foil-var X] : (foil N);


                              (superset X N A);
            ______________________________________________________
                   X : (name A) >> [foil-var X] : (foil N);



                               \\ are these ok?
             ____________________________________________________
                 X : (- (foil [A|AS])) >> X : (- (foil AS));

             ____________________________________________________
                 X : (- (name [A|AS])) >> X : (- (name AS));

                                      )

(datatype @scope-extend@
    ______________________________________________________________________________________________________
           X : (name [A|AS]), XS : (list (foil AS)) >> [[foil-var X] | XS] : (list (foil [A|AS]));

                                                      )

(datatype @scope@

       __________________________
            (- (unify X X));

            (unify (K|T) X);
              (unify Z K);
                   !;
           (unify [X|XS] YS);
    _________________________________
         (superset Z [X|XS] YS);


           (superset Z XS YS);
    _________________________________
         (superset Z [_|XS] YS);

                    )



(datatype @name@
    ______________________________________________________________
                        (foil-new): (name A);

            _____________________________________________
                   cast : ((foil A) --> (foil A));

                                  )




(define foil-add-subst
  { (substitutions AS AS) --> (name AS)
                          --> (foil AS)
                          --> (substitutions AS AS) }

  Set K V -> (alist.set K V Set))

(define exists?
  { B --> (list A) --> boolean }
  X [] -> false
  X [Y|YS] -> (if (== X Y)
                  true
                  (exists? X YS)))


(define foil-sink
  { (substitutions AS AS) --> (name [A|AS])
                          --> (substitutions [A|AS] [A|AS]) }
  Set Witness -> Set)


(define foil-dissolve
  { (name [A|AS]) --> (foil AS)
                  --> (foil [A|AS])
                  --> ((name AS) * (foil AS)) }

  Var Binding Body -> (@p Var Body))


(define foil-add-rename
  { (substitutions AS BS) --> (name [A|AS])
                          --> (foil [B|BS])
                          --> (substitutions [A|AS] [B|BS]) }

  Set K V -> (alist.set K V Set))



(define foil-sub
  { (substitutions A B) --> (foil A) --> (foil B) }

  Sub [foil-apply F | XS] -> [foil-apply F | (map (foil-sub Sub) XS)]

  Sub [foil-var Y] -> (let Expr (alist.value Y Sub)
                         (if (!? Expr)
                             Expr
                             (error "unbound")))

  Sub [foil-let Y X Z] -> (let X* (foil-sub Sub X)
                             (let Y* (foil-new)
                                [foil-let Y* X*
                                          (let Sub (foil-add-rename Sub Y [foil-var Y*])
                                             (foil-sub Sub Z))]))

  Sub [foil-lambda Y Z] -> (let Y*  (foil-new)
                                Sub (foil-add-rename Sub Y [foil-var Y*])
                                Z*  (foil-sub Sub Z)

                              [foil-lambda Y* Z*]))




(define foil-inline
  { (list (name C))
                    --> (substitutions A A)
                    --> (substitutions A B)
                    --> (foil A)
                    --> (foil B) }

  Inline Sub Rename [foil-apply F | XS] -> [foil-apply F | (map (foil-inline Inline Sub Rename) XS)]


  Inline Sub Rename [foil-var Y] -> (let Expr (alist.value Y Sub)
                                       (if (!? Expr)
                                           (foil-inline Inline Sub Rename Expr)

                                           (let Expr (alist.value Y Rename)
                                              (if (!? Expr)
                                                  Expr
                                                  (error "unbound")))))

  Inline Sub Rename [foil-let Y X Z] -> (let YZ* (foil-dissolve Y X Z)
                                             Y* (fst YZ*)
                                             Z* (snd YZ*)
                                             Sub (foil-add-subst Sub Y* X)
                                           (foil-inline Inline Sub Rename Z*))
    where (exists? Y Inline)


  Inline Sub Rename [foil-let Y X Z] -> (let X*     (foil-inline Inline Sub Rename X)
                                             Y*     (foil-new)
                                             Rename (foil-add-rename Rename Y [foil-var Y*])
                                             Sub    (foil-sink Sub Y)
                                             Z*     (foil-inline Inline Sub Rename Z)

                                           [foil-let Y* X* Z*])

  Inline Sub Rename [foil-lambda Y Z] -> (let Y*     (foil-new)
                                              Rename (foil-add-rename Rename Y [foil-var Y*])
                                              Sub    (foil-sink Sub Y)
                                              Z*     (foil-inline Inline Sub Rename Z)

                                            [foil-lambda Y* Z*])
  )



(define foil-curried
  { number --> (list (foil A)) --> symbol --> (foil A) }
  N XS F -> [foil-apply F | (reverse XS)]
    where (<= N 0)

  N XS F -> (let X (foil-new)
               [foil-lambda X (foil-curried (- N 1) [[foil-var X]|XS] F)] ))




\\ Tests

(let
    X (foil-new)
    Y (foil-new)
    Z (foil-new)
    W (foil-new)
    V (foil-new)

  (type [foil-let X [foil-lambda Y [foil-var Y]]
                  [foil-let W [foil-lambda V [foil-var V]]
                            [foil-lambda Z [foil-var X]]]]
        (foil ())))


(let
    A (foil-new)
    B (foil-new)
    C (foil-new)
    D (foil-new)
    E (foil-new)

    Expr  (type [foil-let A [foil-lambda B [foil-apply + [foil-var B] [foil-var B]]]
                          [foil-let C [foil-lambda D [foil-var A]]
                                    [foil-lambda E [foil-apply compose [foil-var C] [foil-var C]]]]]
                (foil ()))

  (foil-inline [A C] [] [] Expr))


(let
    A (foil-new)
    B (foil-new)
    C (foil-new)
    D (foil-new)
    E (foil-new)
    F (foil-new)

    Expr0 (cast [foil-lambda B [foil-apply + [foil-var B] [foil-var B]]])
    Expr1  (cast [foil-let A Expr0
                           [foil-let C [foil-lambda D [foil-var A]]
                                     [foil-lambda E [foil-apply compose [foil-var C] [foil-var C]]]]])

    Expr2 [foil-lambda F Expr1]

  (foil-inline [A C] [] [] Expr2))




\\ these should all fail
\*

(let X (foil-new)
   (type [foil-var X]
         (foil ())))

(let
    X (foil-new)
    Y (foil-new)

  (type [foil-lambda X [foil-var Y]]
        (foil ())))


(let
    X (foil-new)
    Y (foil-new)

  (type [foil-lambda X [foil-lambda X [foil-var X]]]
        (foil ())))

*\
