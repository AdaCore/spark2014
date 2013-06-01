(benchmark xaddlists.4.1
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
    (bit__and Int Int Int )
    (bit__not Int Int Int )
    (bit__or Int Int Int )
    (bit__xor Int Int Int )
    (character__pos Int Int )
    (character__val Int Int )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (nat_list___arr_element nat_list Int Int )
    (nat_list___arr_update nat_list Int Int nat_list )
    (nat_list___bit_eq nat_list nat_list Int )
    (nat_list___mk_const_arr Int nat_list )
    (real___abs real___type real___type )
    (real___bit_eq real___type real___type Int )
    (real___div real___type real___type real___type )
    (real___exp real___type Int real___type )
    (real___minus real___type real___type real___type )
    (real___plus real___type real___type real___type )
    (real___times real___type real___type real___type )
    (real___uminus real___type real___type )
    (round__ real___type Int )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (int___odd Int )
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
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (bit__and ?X ?X ) ?X ) )
  )
  :assumption
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (bit__or ?X ?X ) ?X ) )
  )
  :assumption
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (bit__xor ?X ?X ) 0 ) )
  )
  :assumption
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (bit__and ?X 0 ) 0 ) )
  )
  :assumption
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (bit__or ?X 0 ) ?X ) )
  )
  :assumption
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (bit__xor ?X 0 ) ?X ) )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= 0 (bit__and ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= 0 (bit__or ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= 0 (bit__xor ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= ?X (bit__or ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= ?Y (bit__or ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (- ?X ?Y ) (bit__xor ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (- ?Y ?X ) (bit__xor ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (bit__and ?X ?Y ) ?X )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (bit__and ?X ?Y ) ?Y )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (bit__or ?X ?Y ) (+ ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (bit__xor ?X ?Y ) (+ ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?N Int ) (?X Int ) (?Y Int )
    (implies
      (and
        (<= 0 ?X )
        (<= 0 ?Y )
        (<= 0 ?N )
        (<= ?X (- (int___exp 2 ?N ) 1 ) )
        (<= ?Y (- (int___exp 2 ?N ) 1 ) )
      )
      (<= (bit__or ?X ?Y ) (- (int___exp 2 ?N ) 1 ) )
    )
  )
  :assumption
  (forall
      (?N Int ) (?X Int ) (?Y Int )
    (implies
      (and
        (<= 0 ?X )
        (<= 0 ?Y )
        (<= 0 ?N )
        (<= ?X (- (int___exp 2 ?N ) 1 ) )
        (<= ?Y (- (int___exp 2 ?N ) 1 ) )
      )
      (<= (bit__xor ?X ?Y ) (- (int___exp 2 ?N ) 1 ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (bit__and ?X ?Y ) (bit__or ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (<= 0 ?Y ) )
      (<= (bit__xor ?X ?Y ) (bit__or ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int )
    (implies (<= 0 ?X ) (= (int___abs ?X ) ?X ) )
  )
  :assumption
  (forall
      (?X Int )
    (implies (< ?X 0 ) (= (int___abs ?X ) (~ ?X ) ) )
  )
  :assumption
  (forall
      (?U real___type )
    (implies
      (real___le (int___to_real 0 ) ?U )
      (= (real___abs ?U ) ?U )
    )
  )
  :assumption
  (forall
      (?U real___type )
    (implies
      (real___lt ?U (int___to_real 0 ) )
      (= (real___abs ?U ) (real___uminus ?U ) )
    )
  )
  :assumption
  (forall
      (?X Int )
    (iff (int___odd ?X ) (= (int___mod (int___abs ?X ) 2 ) 1 ) )
  )
  :assumption
  (= 256 256 )
  :assumption
  (= 65536 65536 )
  :assumption
  (= 4294967296 4294967296 )
  :assumption
  (= 18446744073709551616 18446744073709551616 )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies (< 0 ?Y ) (<= 0 (int___mod ?X ?Y ) ) )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies (< 0 ?Y ) (< (int___mod ?X ?Y ) ?Y ) )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies (< ?Y 0 ) (<= (int___mod ?X ?Y ) 0 ) )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies (< ?Y 0 ) (< ?Y (int___mod ?X ?Y ) ) )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< 0 ?Y ) )
      (< (- ?X ?Y ) (* ?Y (int___div ?X ?Y ) ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< 0 ?Y ) )
      (<= (* ?Y (int___div ?X ?Y ) ) ?X )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= ?X 0 ) (< 0 ?Y ) )
      (<= ?X (* ?Y (int___div ?X ?Y ) ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= ?X 0 ) (< 0 ?Y ) )
      (< (* ?Y (int___div ?X ?Y ) ) (+ ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< ?Y 0 ) )
      (<= (* ?Y (int___div ?X ?Y ) ) ?X )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< ?Y 0 ) )
      (< (+ ?X ?Y ) (* ?Y (int___div ?X ?Y ) ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= ?X 0 ) (< ?Y 0 ) )
      (< (* ?Y (int___div ?X ?Y ) ) (- ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= ?X 0 ) (< ?Y 0 ) )
      (<= ?X (* ?Y (int___div ?X ?Y ) ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (= (+ (* ?Y (int___div ?X ?Y ) ) (int___rem ?X ?Y ) ) ?X )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (= (int___rem ?X ?Y ) 0 )
      (= (int___mod ?X ?Y ) 0 )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< 0 ?Y ) )
      (= (int___mod ?X ?Y ) (int___rem ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= ?X 0 ) (< 0 ?Y ) (not (= (int___rem ?X ?Y ) 0 ) ) )
      (= (int___mod ?X ?Y ) (+ (int___rem ?X ?Y ) ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< ?Y 0 ) (not (= (int___rem ?X ?Y ) 0 ) ) )
      (= (int___mod ?X ?Y ) (+ (int___rem ?X ?Y ) ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= ?X 0 ) (< ?Y 0 ) )
      (= (int___mod ?X ?Y ) (int___rem ?X ?Y ) )
    )
  )
  :assumption
  (forall
      (?X Int ) (?Y Int )
    (implies
      (and (<= 0 ?X ) (< ?X ?Y ) )
      (= (int___mod ?X ?Y ) ?X )
    )
  )
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
  :formula
  (and
    (=
      result__index__subtype__1__first
      right__index__subtype__1__first
    )
    (=
      result__index__subtype__1__first
      left__index__subtype__1__first
    )
    (=
      result__index__subtype__1__last
      right__index__subtype__1__last
    )
    (=
      result__index__subtype__1__last
      left__index__subtype__1__last
    )
    (forall
        (?pos_ Int )
      (implies
        (and
          (<= result__index__subtype__1__first ?pos_ )
          (<= ?pos_ result__index__subtype__1__last )
        )
        (and
          (<=
            0
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
    (forall
        (?pos_ Int )
      (implies
        (and
          (<= result__index__subtype__1__first ?pos_ )
          (<= ?pos_ loop__1__i )
        )
        (=
          (nat_list___arr_element result ?pos_ )
          (+
            (nat_list___arr_element left ?pos_ )
            (nat_list___arr_element right ?pos_ )
          )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and
          (<= left__index__subtype__1__first ?i___1 )
          (<= ?i___1 left__index__subtype__1__last )
        )
        (and
          (<= 0 (nat_list___arr_element left ?i___1 ) )
          (<= (nat_list___arr_element left ?i___1 ) natural__last )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and
          (<= right__index__subtype__1__first ?i___1 )
          (<= ?i___1 right__index__subtype__1__last )
        )
        (and
          (<= 0 (nat_list___arr_element right ?i___1 ) )
          (<= (nat_list___arr_element right ?i___1 ) natural__last )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and
          (<= result__index__subtype__1__first ?i___1 )
          (<= ?i___1 result__index__subtype__1__last )
        )
        (and
          (<= 0 (nat_list___arr_element result ?i___1 ) )
          (<= (nat_list___arr_element result ?i___1 ) natural__last )
        )
      )
    )
    (<= 0 loop__1__i )
    (<= loop__1__i natural__last )
    (<= result__index__subtype__1__first loop__1__i )
    (< loop__1__i result__index__subtype__1__last )
    (<= 0 integer__size )
    (<= integer__first integer__last )
    (<= integer__base__first integer__base__last )
    (<= integer__base__first integer__first )
    (<= integer__last integer__base__last )
    (<= 0 natural__size )
    (<= natural__base__first natural__base__last )
    (<= natural__last natural__base__last )
    (<= left__index__subtype__1__last natural__last )
    (<=
      left__index__subtype__1__first
      left__index__subtype__1__last
    )
    (<= left__index__subtype__1__first natural__last )
    (<= right__index__subtype__1__last natural__last )
    (<=
      right__index__subtype__1__first
      right__index__subtype__1__last
    )
    (<= right__index__subtype__1__first natural__last )
    (<= result__index__subtype__1__last natural__last )
    (<=
      result__index__subtype__1__first
      result__index__subtype__1__last
    )
    (<= result__index__subtype__1__first natural__last )
    (<= 0 natural__last )
    (<= natural__base__first 0 )
    (<= 0 left__index__subtype__1__first )
    (<= 0 left__index__subtype__1__last )
    (<= 0 right__index__subtype__1__first )
    (<= 0 right__index__subtype__1__last )
    (<= 0 result__index__subtype__1__first )
    (<= 0 result__index__subtype__1__last )
    (not
      (and
        (<=
          0
          (+
            (nat_list___arr_element left (+ loop__1__i 1 ) )
            (nat_list___arr_element right (+ loop__1__i 1 ) )
          )
        )
        (<=
          (+
            (nat_list___arr_element left (+ loop__1__i 1 ) )
            (nat_list___arr_element right (+ loop__1__i 1 ) )
          )
          natural__last
        )
      )
    )
  )
  :status unknown
)
