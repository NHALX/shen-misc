\\ Multiple return values via Church encoded pairs and CPS.

(synonyms (Z : A , B) ((A --> B --> Z) --> Z))


(define ##.let/k-apply-k
  [lambda|XS] C -> [[lambda|XS] C]
  X           C -> (append X [C]))

(define ##.let/k
  [X]         -> X
  [VS X | XS] -> (let C (append [/. | VS] [(##.let/k XS)])
                    (##.let/k-apply-k X C))
    where (cons? VS)
  [V X | XS]  -> [[/. V (##.let/k XS)] X])

(defmacro macro.let/k
  [let/k X]    -> [let/k X]
  [let/k | XS] -> (##.let/k XS))

(defmacro macro....
  [... | XS] -> (let K# (gensym (protect K))
                   [lambda K# [K# | XS]]))

\*

(let/k
    (A B) (... 1 2)
  (+ A B))

\\ is 3

(macroexpand
 [let/k
     [A B] [... 1 2]
   [+ A B]])

\\ is

[lambda K80493 [K80493 1 2 [lambda A [lambda B [+ A B]]]]]

*\
