
(synonyms var symbol)
(synonyms env (list (symbol * a)))


\\ Syntax of direct-style source language

(datatype ds
            X : var;
       ==================
        [ds.var X] : ds;

            X : var;
            Y : ds;
    ========================
       [ds.fn X Y] : ds;

            X : ds;
            Y : ds;
      ====================
      [ds.apply X Y] : ds;

            X : ds;
            Y : ds;
            Z : ds;
    =======================
      [ds.if X Y Z] : ds;

               )


\\ Syntax of CPS target language

(datatype p
            X : triv;
            Y : triv;
            Z : cont;
     =======================
       [p.call X Y Z] : p;

            X : cont;
            Y : triv;
     =======================
         [p.ret X Y] : p;

            X : triv;
              Y : p;
              Z : p;
     =======================
        [p.if X Y Z] : p;

             X : var;
            Y : cont;
              Z : p;
     =======================
        [p.let X Y Z] : p;


             X : var;
              Y : p;
    ==========================
     [cont.cont X Y] : cont;

             X : var;
    ==========================
       [cont.var X] : cont;

    __________________________
        cont.halt : cont;


             X : var;
             Y : var;
              Z : p;
     =======================
     [triv.lam X Y Z] : triv;

             X : var;
     =======================
      [triv.var X] : triv; )


(define triv.lambda?
  { triv --> boolean }
  [triv.lam _ _ _] -> true
  _ -> false)



\\ Abstract args

(datatype a

          X : var;
    =====================
       [a.var X] : a;

          X : var;
           Y : ds;
          Z : env;
    ====================
      [a.cl X Y Z] : a;

             )

(datatype c

      _____________________
           c.halt : c;

             X : var;
      =====================
          [c.var X] : c;

             X : ds;
             Y : env;
              Z : c;
    ==========================
      [c.cont/f X Y Z] : c;

              X : a;
              Y : c;
      =====================
       [c.cont/a X Y] : c;

             W : ds;
             X : ds;
             Y : env;
              Z : c;
      =====================
     [c.cont/i W X Y Z] : c;

                )

(define c.halt/var?
  { c --> boolean }

  c.halt    -> true
  [c.var _] -> true
  _         -> false)


(define c.cont?
  { c --> boolean }
  [c.cont/i W X Y Z] -> true
  [c.cont/a X Y] -> true
  [c.cont/f X Y Z] -> true)


(define smap.add
  { A --> B
      --> (list (A * B))
      --> (list (A * B)) }

  K V [] -> [(@p K V)]
  K V [(@p K _) | XS] -> [(@p K V) | XS]
  K V [X|XS] -> [X | (smap.add K V XS)])

(define smap.find
  { A --> (list (A * B))
      --> B }

  K [] -> (error "smap.find: not found")
  K [(@p K V) | XS] -> V
  K [_|XS] -> (smap.find K XS))


(define ##.one-ref?
  { string --> boolean }
  (@s "$" XS) -> true
  _ -> false)

(define one-ref?
  { symbol --> boolean }
  X -> (##.one-ref? (str X)))

(define extend
  { symbol --> a
           --> env
           --> env }
  Y X Env -> (smap.add Y X Env))

(define new-count
  { symbol --> (list (symbol * number))
           --> (list (symbol * number)) }
  X Counts -> (smap.add X 0 Counts))

(define incr
  { symbol --> (list (symbol * number))
           --> (list (symbol * number)) }
  X Counts -> (smap.add X (+ 1 (smap.find X Counts))
                        Counts))

(define cps
  { ds --> env
       --> c
       --> (list (symbol * number))
       --> (Z: p, (list (symbol * number))) }

  [ds.var Y]       Env C Counts -> (ret C (smap.find Y Env) Counts)
  [ds.fn Y E]      Env C Counts -> (ret C [a.cl Y E Env] Counts)
  [ds.apply E1 E2] Env C Counts -> (cps E1 Env [c.cont/f E2 Env C] Counts)
  [ds.if E1 E2 E3] Env C Counts -> (cps E1 Env [c.cont/i E2 E3 Env C] Counts))




(define bless/c
  { c --> (list (symbol * number))
      --> (Z: cont, (list (symbol * number))) }

  c.halt Counts     -> (... cont.halt     Counts)
  [c.var KV] Counts -> (... [cont.var KV] Counts)
  C Counts -> (let/k
                  X              (gensym (protect X))
                  Counts2        (new-count X Counts)
                  (Body Counts3) (ret C [a.var X] Counts2)

                 (... [cont.cont X Body] Counts3))

    where (c.cont? C))


(define eta-check
  { var --> var
        --> p
        --> (list (symbol * number))
        --> (Z: triv, (list (symbol * number))) }

  X K [p.call F [triv.var X*] [cont.var K*]] Counts* -> (... F Counts*)
    where (and (= X X*)
               (= K K*)
               (= 1 (smap.find X Counts*)))

  X K B Counts* -> (... [triv.lam X K B] Counts*))

(define bless/a
  { a --> (list (symbol * number))
      --> (Z: triv, (list (symbol * number))) }

  [a.var X] Counts -> (... [triv.var X] (incr X Counts))
  [a.cl Y Body Env] Counts -> (let/k
                                  X           (gensym Y)
                                  K           (gensym (protect K))
                                  Env*        (extend Y [a.var X] Env)
                                  (B Counts*) (cps Body Env* [c.var K]
                                                   (new-count X Counts))

                                (eta-check X K B Counts*)))


(define ret
  { c --> a
      --> (list (symbol * number))
      --> (Z: p, (list (symbol * number))) }

  C A Counts -> (let/k
                    (Cont Counts2) (bless/c C Counts)
                    (Arg Counts3)  (bless/a A Counts2)

                  (... [p.ret Cont Arg] Counts3))

    where (c.halt/var? C)

  [c.cont/f E Env C*] A Counts -> (cps E Env [c.cont/a A C*] Counts)
  [c.cont/a A* C*] A Counts -> (p.call A* A C* Counts)
  [c.cont/i E1 E2 Env C*] A Counts -> (p.if A E1 E2 C* Env Counts))




(define p.call-help
  { a --> c
      --> triv
      --> (list (symbol * number))
      --> (Z: p, (list (symbol * number))) }

  [a.cl Y Body Env] C [triv.var X] Counts2 -> (let Env* (extend Y [a.var X] Env)
                                                 (cps Body Env* C Counts2))

  \*
  We've got a "let" redex, binding y to a lambda term:
  ((FUN y body) (FUN ...))
  We can't reduce this because y has multiple references
  in body, which would replicate the (FUN ...) term. So
  we produce a CPS "let", encoded as a CONT redex:
  (RET (CONT x body') (LAM ...))
    where body' is body cps-converted with the original
  continuation c, and the (LAM ...) term is the
  cps-conversion of the (FUN ...) argument.
  *\

  [a.cl Y Body Env] C Arg Counts2
    -> (let/k
           X           (gensym (protect X))
           Counts3     (new-count X Counts2)
           Env*        (extend Y [a.var X] Env)
           (B Counts4) (cps Body Env* C Counts3)

         (... [p.ret [cont.cont X B] Arg]
              Counts4))

    where (triv.lambda? Arg))



(define p.call
  { a --> a
      --> c
      --> (list (symbol * number))
      --> (Z: p, (list (symbol * number))) }

  [a.var Var] A C Counts -> (let/k
                                (Func Counts2) (bless/a [a.var Var] Counts)
                                (Arg Counts3)  (bless/a A Counts2)
                                (Cont Counts4) (bless/c C Counts3)
                              (... [p.call Func Arg Cont] Counts4))

  [a.cl Y Body Env] A C Counts -> (cps Body (extend Y A Env) C Counts)
    where (one-ref? Y)

  CL A C Counts -> (bless/a A Counts (p.call-help CL C)))



(define p.if
  { a --> ds
      --> ds
      --> c
      --> env
      --> (list (symbol * number))
      --> (Z: p, (list (symbol * number))) }

  A E1 E2 C Env Counts -> (let/k
                              (Test   Counts2) (bless/a A Counts)
                              (Conseq Counts3) (cps E1 Env C Counts2)
                              (Alt    Counts4) (cps E2 Env C Counts3)
                            (... [p.if Test Conseq Alt] Counts4))
    where (c.halt/var? C)

  A E1 E2 C Env Counts -> (let/k
                              JV             (gensym (protect Join))
                              (Body Counts2) (p.if A E1 E2 [c.var JV] Env Counts)
                              (Join Counts3) (bless/c C Counts2)
                            (... [p.let JV Join Body] Counts3))

    where (c.cont? C))



\\ Test: Assumes linear variables are tagged with $ prefix. See paper for details.

(cps [ds.apply [ds.fn $X [ds.var $X]]
               [ds.fn $X [ds.var $X]]]
     [(@p $X [a.var $X])]
     c.halt
     [(@p $X 1)]
     (/. X Y X))


(cps [ds.apply [ds.fn $X [ds.var $X]]
               [ds.var $Y]]
     [(@p $X [a.var $X])
      (@p $Y [a.var $Y])]
     c.halt
     [(@p $X 1) (@p $Y 1)]
     (/. X Y X))
