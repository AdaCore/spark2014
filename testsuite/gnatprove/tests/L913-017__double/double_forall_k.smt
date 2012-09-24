(benchmark linear_search.1.1
  :logic AUFNIRA
  :extrasorts ( intarray real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (intarray___default_arr intarray )
    (intarray___default_arr_element Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (table intarray )
    (table___init intarray )
    (table___loopinit intarray )
    (table__index__subtype__1__base__first Int )
    (table__index__subtype__1__base__last Int )
    (table__index__subtype__1__first Int )
    (table__index__subtype__1__last Int )
    (value Int )
    (value___init Int )
    (value___loopinit Int )
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
    (intarray___arr_box_update intarray Int Int Int intarray )
    (intarray___arr_element intarray Int Int )
    (intarray___arr_update intarray Int Int intarray )
    (intarray___bit_eq intarray intarray Int )
    (intarray___mk_const_arr Int intarray )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
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
  (= integer__first (~ 2147483648 ) )
  :assumption
  (= integer__last 2147483647 )
  :assumption
  (= integer__base__first (~ 2147483648 ) )
  :assumption
  (= integer__base__last 2147483647 )
  :assumption
  (<= integer__first table__index__subtype__1__first )
  :assumption
  (<= table__index__subtype__1__last integer__last )
  :assumption
  (<=
    table__index__subtype__1__first
    table__index__subtype__1__last
  )
  :assumption
  (<= integer__first table__index__subtype__1__last )
  :assumption
  (<= table__index__subtype__1__first integer__last )
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
      (?x intarray ) (?y intarray )
    (iff (= (intarray___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
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
      (intarray___arr_element (intarray___mk_const_arr ?v ) ?i1 )
      ?v
    )
  )
  :assumption
  (forall
      (?a intarray ) (?s0 Int ) (?t Int )
    (=
      (intarray___arr_element
        (intarray___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a intarray ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (intarray___arr_element
          (intarray___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (intarray___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a intarray )
      (?s0 Int )
      (?s0p Int )
      (?s0q Int )
      (?t Int )
    (implies
      (and (<= ?s0p ?s0 ) (<= ?s0 ?s0q ) )
      (=
        (intarray___arr_element
          (intarray___arr_box_update ?a ?s0p ?s0q ?t )
          ?s0
        )
        ?t
      )
    )
  )
  :assumption
  (forall
      (?a intarray )
      (?s0 Int )
      (?s0p Int )
      (?s0q Int )
      (?t Int )
    (or
      (and (<= ?s0p ?s0 ) (<= ?s0 ?s0q ) )
      (=
        (intarray___arr_element
          (intarray___arr_box_update ?a ?s0p ?s0q ?t )
          ?s0
        )
        (intarray___arr_element ?a ?s0 )
      )
    )
  )
  :formula
  (and
    (or
      (forall
          (?k_ Int )
        (implies
          (and
            (<= table__index__subtype__1__first ?k_ )
            (<= ?k_ (- loop__1__i 1 ) )
          )
          (=
            (intarray___arr_element table ?k_ )
            (intarray___arr_element table loop__1__i )
          )
        )
      )
      (forall
          (?k_ Int )
        (implies
          (and
            (<= table__index__subtype__1__first ?k_ )
            (<= ?k_ (- loop__1__i 1 ) )
          )
          (not
            (=
              (intarray___arr_element table ?k_ )
              (intarray___arr_element table loop__1__i )
            )
          )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and
          (<= table__index__subtype__1__first ?i___1 )
          (<= ?i___1 table__index__subtype__1__last )
        )
        (and
          (<= (~ 2147483648 ) (intarray___arr_element table ?i___1 ) )
          (<= (intarray___arr_element table ?i___1 ) 2147483647 )
        )
      )
    )
    (<=
      (~ 2147483648 )
      (intarray___arr_element table loop__1__i )
    )
    (<= (intarray___arr_element table loop__1__i ) 2147483647 )
    (<= (~ 2147483648 ) loop__1__i )
    (<= loop__1__i 2147483647 )
    (<= table__index__subtype__1__first loop__1__i )
    (< loop__1__i table__index__subtype__1__last )
    (<= 0 integer__size )
    (<=
      table__index__subtype__1__first
      table__index__subtype__1__last
    )
    (<= (~ 2147483648 ) table__index__subtype__1__first )
    (<= (~ 2147483648 ) table__index__subtype__1__last )
    (<= table__index__subtype__1__last 2147483647 )
    (<= table__index__subtype__1__first 2147483647 )
    (not
      (or
        (forall
            (?k_ Int )
          (implies
            (and
              (<= table__index__subtype__1__first ?k_ )
              (<= ?k_ loop__1__i )
            )
            (=
              (intarray___arr_element table ?k_ )
              (intarray___arr_element table loop__1__i )
            )
          )
        )
        (forall
            (?k_ Int )
          (implies
            (and
              (<= table__index__subtype__1__first ?k_ )
              (<= ?k_ loop__1__i )
            )
            (not
              (=
                (intarray___arr_element table ?k_ )
                (intarray___arr_element table loop__1__i )
              )
            )
          )
        )
      )
    )
  )
  :status unknown
)
