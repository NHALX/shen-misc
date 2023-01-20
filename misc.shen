(tc -) \\ untyped


\\ system patch

(package shen [&]

 (define map-expr
   F [] -> []
   F [L|R] -> [(F L) | (map-expr F R)]
   F X -> (F X))

(define prterm
  [cons X Y] -> (do (pr "[") (prterm X) (prtl Y) (pr "]"))
  [F | X] -> (do (pr "(") (prterm F) (map-expr (/. Y (do (pr " ") (prterm Y))) X) (pr ")"))
  X -> (print X))

 )



(tc +)
\\ typed

\\ unit module

(datatype @unit@
    __________________________
          unit : unit;)

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


 (define alist.foldl
   { (C --> A --> B --> C) --> (alist.alist A B) --> C --> C }
   F [] C -> C
   F [(@p A B)|XS] C -> (alist.foldl F XS (F C A B)))

\\ list

(define foldl
   { (B --> A --> B) --> (list A) --> B --> B }
   F [] B -> B
   F [X|XS] B -> (foldl F XS (F B X)))


(datatype @unify@
    _______________________
         (unify X X);)
