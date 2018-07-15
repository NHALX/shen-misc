(specialise <-record)
(specialise @r)

(package record [@r <-record record just nothing]

 (define field-typeof
   [record X | XS] 1 -> [just X]
   [record X | XS] N -> (field-typeof [record | XS] (- N 1)) where (> N 1)
   _               _ -> nothing)

 (define const-index?
   I -> (>= I 1) where (number? I)
   N -> (error "record: invalid index: ~A" N))

 (define <-record
   X I -> (<-vector X I))

 (define @r
   A B -> (@v A B)) )


(systemf record)
(systemf <-record)
(systemf @r)


(datatype record

           ________________________
                   (X ~ X);

           ________________________
                <> : (record);

                    X : L;
              Y : (record | TS);
         ____________________________
          (@r X Y) : (record L | TS);


               \\ field metadata
      let Maybe (record.field-typeof T I)
              ((just Z) ~ Maybe);
    _______________________________________
       (record.field-type-unify T I Z);


          if (record.const-index? I)
                    V : T;
       (record.field-type-unify T I Z);
     _____________________________________
             (<-record V I) : Z; )



\\ Typechecks in 77 inferences:
\\ (<-record (@r 1 (@r true <>)) 2)
