(benchmark f7.4.1
  :logic AUFNIRA
  :extrasorts ( real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (w Int )
    (w___init Int )
    (w___loopinit Int )
    (x Int )
    (x___init Int )
    (x___loopinit Int )
    (y Int )
    (y___init Int )
    (y___loopinit Int )
    (z Int )
    (z___init Int )
    (z___loopinit Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (f4 Int Int Int )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (real___bit_eq real___type real___type Int )
    (round__ real___type Int )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (<= 0 integer__size )
  :assumption
  (<= integer__first integer__last )
  :assumption
  (<= integer__base__first integer__base__last )
  :assumption
  (<= integer__base__first integer__first )
  :assumption
  (<= integer__last integer__base__last )
  :assumption
  (<= 0 integer__size )
  :assumption
  (<= integer__first integer__last )
  :assumption
  (<= integer__base__first integer__base__last )
  :assumption
  (<= integer__base__first integer__first )
  :assumption
  (<= integer__last integer__base__last )
  :assumption
  (forall
      (?x Int )
    (iff
      (bit___type___member ?x )
      (and (<= 0 ?x ) (<= ?x 1 ) )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (bit___and ?x ?y ) bit___true )
      (and (= ?x bit___true ) (= ?y bit___true ) )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (bit___or ?x ?y ) bit___true )
      (or (= ?x bit___true ) (= ?y bit___true ) )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (bit___iff ?x ?y ) bit___true )
      (iff (= ?x bit___true ) (= ?y bit___true ) )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (= (bit___not ?x ) bit___true )
      (not (= ?x bit___true ) )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff (= (integer___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x real___type ) (?y real___type )
    (iff (= (real___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (bit___type___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff (= (integer___bit_le ?x ?y ) bit___true ) (<= ?x ?y ) )
  )
  :assumption
  (= bit___false 0 )
  :assumption
  (= bit___true 1 )
  :assumption
  true
  :assumption
  (<= integer__first w )
  :assumption
  (<= w integer__last )
  :assumption
  (<= integer__first x )
  :assumption
  (<= x integer__last )
  :assumption
  (<= integer__first y )
  :assumption
  (<= y integer__last )
  :assumption
  (<= integer__first z )
  :assumption
  (<= z integer__last )
  :assumption
  (<= integer__first z )
  :assumption
  (<= z integer__last )
  :assumption
  (<= integer__first y )
  :assumption
  (<= y integer__last )
  :assumption
  (<= integer__first x )
  :assumption
  (<= x integer__last )
  :assumption
  (<= integer__first w )
  :assumption
  (<= w integer__last )
  :assumption
  (<= integer__first (f4 y z ) )
  :assumption
  (<= (f4 y z ) integer__last )
  :assumption
  (implies (<= z y ) (= (f4 y z ) y ) )
  :assumption
  (implies (< y z ) (= (f4 y z ) z ) )
  :assumption
  (<= integer__first (f4 y z ) )
  :assumption
  (<= (f4 y z ) integer__last )
  :assumption
  (<= integer__first (f4 x (f4 y z ) ) )
  :assumption
  (<= (f4 x (f4 y z ) ) integer__last )
  :assumption
  (implies (<= (f4 y z ) x ) (= (f4 x (f4 y z ) ) x ) )
  :assumption
  (implies (< x (f4 y z ) ) (= (f4 x (f4 y z ) ) (f4 y z ) ) )
  :assumption
  (<= integer__first (f4 x (f4 y z ) ) )
  :assumption
  (<= (f4 x (f4 y z ) ) integer__last )
  :assumption
  (<= integer__first (f4 w (f4 x (f4 y z ) ) ) )
  :assumption
  (<= (f4 w (f4 x (f4 y z ) ) ) integer__last )
  :assumption
  (implies
    (<= (f4 x (f4 y z ) ) w )
    (= (f4 w (f4 x (f4 y z ) ) ) w )
  )
  :assumption
  (implies
    (< w (f4 x (f4 y z ) ) )
    (= (f4 w (f4 x (f4 y z ) ) ) (f4 x (f4 y z ) ) )
  )
  :formula
  (not
    (and
      (implies
        (and (<= x w ) (and (<= y w ) (<= z w ) ) )
        (= (f4 w (f4 x (f4 y z ) ) ) w )
      )
      (implies
        (and (< w x ) (and (<= y x ) (<= z x ) ) )
        (= (f4 w (f4 x (f4 y z ) ) ) x )
      )
      (implies
        (and (< w y ) (and (< x y ) (<= z y ) ) )
        (= (f4 w (f4 x (f4 y z ) ) ) y )
      )
      (implies
        (and (< w z ) (and (< x z ) (< y z ) ) )
        (= (f4 w (f4 x (f4 y z ) ) ) z )
      )
      (<= integer__first (f4 w (f4 x (f4 y z ) ) ) )
      (<= (f4 w (f4 x (f4 y z ) ) ) integer__last )
    )
  )
  :status unknown
)
