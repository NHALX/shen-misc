
\* Toposort probably isn't bringing much performance,
   but I'm retaining it for now. *\

(package chain []

 (define list.foldl
   { (B --> A --> B) --> B --> (list A) --> B }
   F Z []     -> Z
   F Z [X|XS] -> (list.foldl F (F Z X) XS))

 (define list.insert
   { (A --> A --> boolean) --> A
                           --> (list A)
                           --> (list A) }

   GT X [Y|YS] -> [Y | (list.insert GT X YS)] where (GT X Y)
   GT X YS     -> [X | YS])


 (define list.insertion-sort
   { (A --> A --> boolean) --> (list A)
                           --> (list A) }

   GT XS -> (list.foldl (/. B A (list.insert GT A B)) [] XS))


 (define list.prioritize
   { (A --> number) --> (list A)
                    --> (list A) }

   P XS -> (list.insertion-sort (/. A B (< (P A) (P B))) XS))


 (define list.filter
   { (A --> boolean) --> (list A)
                     --> (list A) }
   F []     -> []
   F [X|XS] -> (if (F X)
                   [X | (list.filter F XS)]
                   (list.filter F XS)))


 (define list.exists
   { (A --> boolean) --> (list A)
                     --> boolean }

   F []     -> false
   F [X|XS] -> true where (F X)
   F [_|XS] -> (list.exists F XS))


 (define p.eq
   { (A --> B) --> A --> A --> boolean }
   P A B -> (= (P A) (P B)))

 (define p.neq
   { (A --> B) --> A --> A --> boolean }
   P A B -> (not (= (P A) (P B))))

 (define car
   [] -> []
   X  -> [(head X)])

 (define cdr
   [] -> []
   X  -> [(tail X)])

 \\\\\\\\\\


 (define ##.head-not-in-tails
   P TS []     -> (error "no linearization")
   P TS [X|XS] -> (if (list.exists (list.exists (p.eq P X)) TS)
                      (##.head-not-in-tails P TS XS)
                      X))


 (define head-not-in-tails
   P R L -> (let HS  (mapcan (function car) L)
                 TS  (mapcan (function cdr) L)
                 RHS (list.prioritize R HS)

               (##.head-not-in-tails P TS RHS)))


 (define ##.remove
   P X XS -> (list.filter (p.neq P X) XS))

 (define discard
   P X XS -> (list.filter (function cons?)
                          (map (##.remove P X) XS)))


 (define cut-minimal
   P R XS K -> (let X (head-not-in-tails P R XS)
                    N (discard P X XS)
                  (K X N)))


 \* This is similar to Kahn's algorithm but assumes that elements of the input
  * poset are already sorted into groups of chains.
  *\

 (define sort
   P R [] -> []
   P R Z  -> (cut-minimal P R Z (/. X XS [X | (sort P R XS)])))
 )


(package pattern [chain.sort]


 (define rewrite.postorder
   F [X|XS] -> (F [(rewrite.postorder F X) | (rewrite.postorder F XS)])
   F X      -> (F X))

 (define rewrite.atom
   F [X|XS] -> [(rewrite.atom F X) | (rewrite.atom F XS)]
   F X      -> (F X))

 (define meta-lambda
   []     B -> B
   [V|VS] B -> [lambda V (meta-lambda VS B)])

 (define variables
   [L|R] ZS -> (variables L (variables R ZS))
   X ZS     -> (adjoin X ZS) where (variable? X)
   _ ZS     -> ZS)


 (define ##.substitute
   Env X -> (let Y (assoc X Env)
               (if (cons? Y)
                   (tail Y)
                   X))
     where (variable? X)
   Env X -> X)

 (define substitute
   Env Expr -> (rewrite.atom (##.substitute Env) Expr))

 \\\\\\\\

 (define priority
   [alias _ _] -> 0
   [bind _ _] -> 1
   [guard _] -> 2)


 (define ##.apply
   [] ST [] -> ST
   [F|FS] ST [X|XS] -> (##.apply FS (F ST X) XS))

 (define pattern.fold
   F G R-ST W-ST [Head | XS] -> (let
                                    RS-W-ST* (F Head (length XS) R-ST W-ST)
                                    RS       (fst RS-W-ST*)
                                    W-ST*    (snd RS-W-ST*)
                                    FS       (map (pattern.fold F G) RS)

                                  (##.apply FS W-ST* XS))

   F G R-ST W-ST X -> (G X R-ST W-ST) \\where (symbol? X)
   )


 (define ##.bin
   G H T (@p Var XS) ZS -> (let
                               \\HD (concat Var (concat / H))
                               \\TL (concat Var (concat / T))
                               HD     (gensym Var)
                               TL     (gensym Var)
                               KHD    [bind HD [H Var]]
                               KTL    [bind TL [T Var]]
                               KGUARD [guard [G Var]]

                             (@p [(@p HD [KHD KGUARD | XS])
                                  (@p TL [KTL KGUARD | XS])]

                                 ZS)))

 (define ##.expr
   cons 2 S1 S2 -> (##.bin cons? hd tl S1 S2)
   join 2 S1 S2 -> (##.bin pair? left right S1 S2)
   @v   2 S1 S2 -> (##.bin +vector? hdv tlv S1 S2)
   @s   2 S1 S2 -> (##.bin +string? hdstr tlstr S1 S2)
   @p   2 S1 S2 -> (##.bin tuple? fst snd S1 S2))


 (define ##.atom
   Sym (@p V XS) ZS -> (let VAR V \\VAR (concat V /VAR)
                            Y   [alias Sym VAR]
                            Z   (reverse [Y|XS])

                          [Z|ZS])
     where (variable? Sym)

   Const (@p V XS) ZS -> (if (= Const _)
                             ZS
                             (let Y [guard [= Const V]]
                                  Z (reverse [Y|XS])
                                [Z|ZS])))


 (define patterns->chains
   []       []           Z -> Z
   [Var|VS] [Pattern|PS] Z -> (let Z* (pattern.fold (function ##.expr)
                                                    (function ##.atom)
                                                    (@p Var [])
                                                    Z
                                                    Pattern)

                                 (patterns->chains VS PS Z*))

   A B _ -> (error "patterns->chains: missing pattern or parameter: ~A / ~A" A B))





 (define indirections
   [F X] -> (+ 1 (indirections X))
   X     -> 0)

 (set *pattern.max-indirections* 3)


 (define ##.assign
   K V (@p Alias Env) -> (@p Alias [[K|V] | Env]))

 (define ##.env
   Expr (@p Alias Env) -> (substitute Env Expr))

 (define ##.alias?
   X (@p Alias Env) -> (element? X Alias))

 (define ##.alias
   X (@p Alias Env) -> (@p [X|Alias] Env))


 (define ir->kl
   ST Body _ [] -> (##.env Body ST)

   ST Body Next [[guard X] | XS]
     -> (let X*   (##.env X ST)
             Expr (ir->kl ST Body Next XS)

           [if X* Expr Next])

   ST Body Next [[bind X Y] | XS]

     -> (let Y* (##.env Y ST)
           (if (< (indirections Y*) (value *pattern.max-indirections*))
               (ir->kl (##.assign X Y* ST) Body Next XS)

               [let X Y*
                  (ir->kl ST Body Next XS)]))

   ST Body Next [[alias X Y] | XS]
     -> (let X*   (##.env X ST)
             Y*   (##.env Y ST)
             Expr (ir->kl ST Body Next XS)

           [if [= X* Y*] Expr Next])

     where (##.alias? X ST)

   ST Body Next [[alias X Y] | XS]
     -> (let Y*  (##.env Y ST)
             ST* (##.alias X (##.assign X Y* ST))
           (ir->kl ST* Body Next XS))

   _ _ _ Expr -> (error "ir->kl: unhandled: ~A" Expr))




 (define ##.if->and
   [if Test1 [if Test2 X Y] Y] -> [if [and Test1 Test2] X Y]
   X -> X)

 (define if->and
   XS -> (rewrite.postorder (function ##.if->and) XS))


 (define pattern
   Accept Pass IR -> (if->and (ir->kl (@p [] []) Accept Pass IR)))


 (define rule
   Params Patterns Accept Pass -> (let IR (chain.sort
                                           (/. X X)
                                           (function priority)
                                           (patterns->chains Params Patterns []))

                                     (pattern Accept Pass IR)))


 (define rules->kl
   Default _ [] -> Default

   Default Params [(@p [match Backtrack? Patterns Guard] Body) | RS]
     -> (let Fail# (gensym (protect Pass))
             Ok#   (gensym (protect Accept))
             VS    (variables Patterns [])
             Next  (meta-lambda Params (rules->kl Default Params RS))
             Pass  [Fail# | Params]
             Accept (if Backtrack?
                        (let Result# (gensym (protect Result))
                           [let Result# [Ok# | VS]
                              [if [= Result# [fail]]
                                  [Fail# | Params]
                                  Result#]])

                        [Ok# | VS])

             Enter (if (= Guard true)
                       Accept
                       [if Guard Accept Pass])

           [let Ok# (meta-lambda VS Body)
              [let Fail# Next
                 (rule Params Patterns Enter Pass)]]))
 )



\*

(eval
 [defun test9 [Var1]
   (pattern.rules->kl
    false  \\ Failure branch
    [Var1] \\ Parameter vars
    [(@p [pattern.match 
                  true         \\ backtrack flag
                  [[cons 1 X]] \\ list of patterns - must be same length as parameter list
                  [= X 9]]     \\ guard
         [fail]  \\ function body
)])])

(let Var [1|9]
   (scm.time (test9 Var)))
*\
