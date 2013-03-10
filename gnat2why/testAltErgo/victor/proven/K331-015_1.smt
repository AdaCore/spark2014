(benchmark zero_n_to_m.1.1
  :logic AUFNIRA
  :extrasorts ( naturals real___type )
  :extrafuns 
  ( (a naturals )
    (a___init naturals )
    (a___loopinit naturals )
    (a__index__subtype__1__base__first Int )
    (a__index__subtype__1__base__last Int )
    (a__index__subtype__1__first Int )
    (a__index__subtype__1__last Int )
    (bit___false Int )
    (bit___true Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (m Int )
    (m___init Int )
    (m___loopinit Int )
    (n Int )
    (n___init Int )
    (n___loopinit Int )
    (natural__base__first Int )
    (natural__base__last Int )
    (natural__first Int )
    (natural__last Int )
    (natural__size Int )
    (naturals___default_arr naturals )
    (naturals___default_arr_element Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (naturals___arr_element naturals Int Int )
    (naturals___arr_update naturals Int Int naturals )
    (naturals___bit_eq naturals naturals Int )
    (naturals___mk_const_arr Int naturals )
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
  (<= 0 natural__size )
  :assumption
  (= natural__first 0 )
  :assumption
  (<= natural__first natural__last )
  :assumption
  (<= natural__base__first natural__base__last )
  :assumption
  (<= natural__base__first natural__first )
  :assumption
  (<= natural__last natural__base__last )
  :assumption
  (<= natural__first a__index__subtype__1__first )
  :assumption
  (<= a__index__subtype__1__last natural__last )
  :assumption
  (<= a__index__subtype__1__first a__index__subtype__1__last )
  :assumption
  (<= natural__first a__index__subtype__1__last )
  :assumption
  (<= a__index__subtype__1__first natural__last )
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
  (<= 0 natural__size )
  :assumption
  (= natural__first 0 )
  :assumption
  (<= natural__first natural__last )
  :assumption
  (<= natural__base__first natural__base__last )
  :assumption
  (<= natural__base__first natural__first )
  :assumption
  (<= natural__last natural__base__last )
  :assumption
  (<= natural__first a__index__subtype__1__first )
  :assumption
  (<= a__index__subtype__1__last natural__last )
  :assumption
  (<= a__index__subtype__1__first a__index__subtype__1__last )
  :assumption
  (<= natural__first a__index__subtype__1__last )
  :assumption
  (<= a__index__subtype__1__first natural__last )
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
      (?x naturals ) (?y naturals )
    (iff (= (naturals___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
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
  (forall
      (?i1 Int ) (?v Int )
    (=
      (naturals___arr_element (naturals___mk_const_arr ?v ) ?i1 )
      ?v
    )
  )
  :assumption
  (forall
      (?a naturals ) (?s0 Int ) (?t Int )
    (=
      (naturals___arr_element
        (naturals___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a naturals ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (naturals___arr_element
          (naturals___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (naturals___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  true
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= a__index__subtype__1__first ?i___1 )
        (<= ?i___1 a__index__subtype__1__last )
      )
      (and
        (<= natural__first (naturals___arr_element a ?i___1 ) )
        (<= (naturals___arr_element a ?i___1 ) natural__last )
      )
    )
  )
  :assumption
  (<= natural__first n )
  :assumption
  (<= n natural__last )
  :assumption
  (<= natural__first m )
  :assumption
  (<= m natural__last )
  :assumption
  (<= integer__first (- m 1 ) )
  :assumption
  (<= (- m 1 ) integer__last )
  :assumption
  (<= integer__base__first (- m 1 ) )
  :assumption
  (<= (- m 1 ) integer__base__last )
  :assumption
  (<= integer__first n )
  :assumption
  (<= n integer__last )
  :formula
  (not
    (and
      (implies
        (<= n (- m 1 ) )
        (and
          (<= natural__first (- m 1 ) )
          (<= (- m 1 ) natural__last )
        )
      )
      (implies
        (<= n (- m 1 ) )
        (and (<= natural__first n ) (<= n natural__last ) )
      )
    )
  )
  :status unknown
)
