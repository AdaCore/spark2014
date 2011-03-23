(benchmark xaddlists.1.1
  :logic AUFNIRA
  :extrasorts ( nat_list real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (left nat_list )
    (left___init nat_list )
    (left___loopinit nat_list )
    (left__index__subtype__1__base__first Int )
    (left__index__subtype__1__base__last Int )
    (left__index__subtype__1__first Int )
    (left__index__subtype__1__last Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (nat_list___default_arr nat_list )
    (nat_list___default_arr_element Int )
    (natural__base__first Int )
    (natural__base__last Int )
    (natural__first Int )
    (natural__last Int )
    (natural__size Int )
    (result nat_list )
    (result___init nat_list )
    (result___loopinit nat_list )
    (result__index__subtype__1__base__first Int )
    (result__index__subtype__1__base__last Int )
    (result__index__subtype__1__first Int )
    (result__index__subtype__1__last Int )
    (right nat_list )
    (right___init nat_list )
    (right___loopinit nat_list )
    (right__index__subtype__1__base__first Int )
    (right__index__subtype__1__base__last Int )
    (right__index__subtype__1__first Int )
    (right__index__subtype__1__last Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (nat_list___arr_element nat_list Int Int )
    (nat_list___arr_update nat_list Int Int nat_list )
    (nat_list___bit_eq nat_list nat_list Int )
    (nat_list___mk_const_arr Int nat_list )
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
  (<= natural__first left__index__subtype__1__first )
  :assumption
  (<= left__index__subtype__1__last natural__last )
  :assumption
  (<=
    left__index__subtype__1__first
    left__index__subtype__1__last
  )
  :assumption
  (<= natural__first left__index__subtype__1__last )
  :assumption
  (<= left__index__subtype__1__first natural__last )
  :assumption
  (<= natural__first right__index__subtype__1__first )
  :assumption
  (<= right__index__subtype__1__last natural__last )
  :assumption
  (<=
    right__index__subtype__1__first
    right__index__subtype__1__last
  )
  :assumption
  (<= natural__first right__index__subtype__1__last )
  :assumption
  (<= right__index__subtype__1__first natural__last )
  :assumption
  (<= natural__first result__index__subtype__1__first )
  :assumption
  (<= result__index__subtype__1__last natural__last )
  :assumption
  (<=
    result__index__subtype__1__first
    result__index__subtype__1__last
  )
  :assumption
  (<= natural__first result__index__subtype__1__last )
  :assumption
  (<= result__index__subtype__1__first natural__last )
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
  (<= natural__first left__index__subtype__1__first )
  :assumption
  (<= left__index__subtype__1__last natural__last )
  :assumption
  (<=
    left__index__subtype__1__first
    left__index__subtype__1__last
  )
  :assumption
  (<= natural__first left__index__subtype__1__last )
  :assumption
  (<= left__index__subtype__1__first natural__last )
  :assumption
  (<= natural__first right__index__subtype__1__first )
  :assumption
  (<= right__index__subtype__1__last natural__last )
  :assumption
  (<=
    right__index__subtype__1__first
    right__index__subtype__1__last
  )
  :assumption
  (<= natural__first right__index__subtype__1__last )
  :assumption
  (<= right__index__subtype__1__first natural__last )
  :assumption
  (<= natural__first result__index__subtype__1__first )
  :assumption
  (<= result__index__subtype__1__last natural__last )
  :assumption
  (<=
    result__index__subtype__1__first
    result__index__subtype__1__last
  )
  :assumption
  (<= natural__first result__index__subtype__1__last )
  :assumption
  (<= result__index__subtype__1__first natural__last )
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
      (?x nat_list ) (?y nat_list )
    (iff (= (nat_list___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
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
      (nat_list___arr_element (nat_list___mk_const_arr ?v ) ?i1 )
      ?v
    )
  )
  :assumption
  (forall
      (?a nat_list ) (?s0 Int ) (?t Int )
    (=
      (nat_list___arr_element
        (nat_list___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a nat_list ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (nat_list___arr_element
          (nat_list___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (nat_list___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (=
    result__index__subtype__1__first
    right__index__subtype__1__first
  )
  :assumption
  (=
    result__index__subtype__1__first
    left__index__subtype__1__first
  )
  :assumption
  (=
    result__index__subtype__1__last
    right__index__subtype__1__last
  )
  :assumption
  (=
    result__index__subtype__1__last
    left__index__subtype__1__last
  )
  :assumption
  (forall
      (?pos_ Int )
    (implies
      (and
        (<= result__index__subtype__1__first ?pos_ )
        (<= ?pos_ result__index__subtype__1__last )
      )
      (and
        (<=
          natural__first
          (+
            (nat_list___arr_element left ?pos_ )
            (nat_list___arr_element right ?pos_ )
          )
        )
        (<=
          (+
            (nat_list___arr_element left ?pos_ )
            (nat_list___arr_element right ?pos_ )
          )
          natural__last
        )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= left__index__subtype__1__first ?i___1 )
        (<= ?i___1 left__index__subtype__1__last )
      )
      (and
        (<= natural__first (nat_list___arr_element left ?i___1 ) )
        (<= (nat_list___arr_element left ?i___1 ) natural__last )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= right__index__subtype__1__first ?i___1 )
        (<= ?i___1 right__index__subtype__1__last )
      )
      (and
        (<= natural__first (nat_list___arr_element right ?i___1 ) )
        (<= (nat_list___arr_element right ?i___1 ) natural__last )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= result__index__subtype__1__first ?i___1 )
        (<= ?i___1 result__index__subtype__1__last )
      )
      (and
        (<= natural__first (nat_list___arr_element result ?i___1 ) )
        (<= (nat_list___arr_element result ?i___1 ) natural__last )
      )
    )
  )
  :formula
  (not
    (and
      (<= integer__first result__index__subtype__1__last )
      (<= result__index__subtype__1__last integer__last )
      (<= integer__first result__index__subtype__1__first )
      (<= result__index__subtype__1__first integer__last )
    )
  )
  :status unknown
)
