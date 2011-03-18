(benchmark block_copy2.18.1
  :logic AUFNIRA
  :extrasorts ( word32_array_type real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (dest word32_array_type )
    (dest___init word32_array_type )
    (dest___loopinit word32_array_type )
    (dest__index__subtype__1__base__first Int )
    (dest__index__subtype__1__base__last Int )
    (dest__index__subtype__1__first Int )
    (dest__index__subtype__1__last Int )
    (index__base__first Int )
    (index__base__last Int )
    (index__first Int )
    (index__last Int )
    (index__size Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (loop__2__i Int )
    (loop__2__i___init Int )
    (loop__2__i___loopinit Int )
    (source word32_array_type )
    (source___init word32_array_type )
    (source___loopinit word32_array_type )
    (source__index__subtype__1__base__first Int )
    (source__index__subtype__1__base__last Int )
    (source__index__subtype__1__first Int )
    (source__index__subtype__1__last Int )
    (word32__base__first Int )
    (word32__base__last Int )
    (word32__first Int )
    (word32__last Int )
    (word32__modulus Int )
    (word32__size Int )
    (word32_array_type___default_arr word32_array_type )
    (word32_array_type___default_arr_element Int )
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
    (index___bit_eq Int Int Int )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
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
    (word32___bit_eq Int Int Int )
    (word32_array_type___arr_element word32_array_type Int Int )
    (word32_array_type___arr_update
      word32_array_type
      Int
      Int
      word32_array_type
    )
    (word32_array_type___bit_eq
      word32_array_type
      word32_array_type
      Int
    )
    (word32_array_type___mk_const_arr Int word32_array_type )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (int___odd Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (<= 0 index__size )
  :assumption
  (= index__first 0 )
  :assumption
  (= index__last 79 )
  :assumption
  (<= index__base__first index__base__last )
  :assumption
  (<= index__base__first index__first )
  :assumption
  (<= index__last index__base__last )
  :assumption
  (<= 0 word32__size )
  :assumption
  (= word32__first 0 )
  :assumption
  (= word32__last 4294967295 )
  :assumption
  (= word32__base__first 0 )
  :assumption
  (= word32__base__last 4294967295 )
  :assumption
  (= word32__modulus 4294967296 )
  :assumption
  (<= index__first source__index__subtype__1__first )
  :assumption
  (<= source__index__subtype__1__last index__last )
  :assumption
  (<=
    source__index__subtype__1__first
    source__index__subtype__1__last
  )
  :assumption
  (<= index__first source__index__subtype__1__last )
  :assumption
  (<= source__index__subtype__1__first index__last )
  :assumption
  (<= index__first dest__index__subtype__1__first )
  :assumption
  (<= dest__index__subtype__1__last index__last )
  :assumption
  (<=
    dest__index__subtype__1__first
    dest__index__subtype__1__last
  )
  :assumption
  (<= index__first dest__index__subtype__1__last )
  :assumption
  (<= dest__index__subtype__1__first index__last )
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
      (?x Int ) (?y Int )
    (iff (= (index___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff (= (word32___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x word32_array_type ) (?y word32_array_type )
    (iff
      (= (word32_array_type___bit_eq ?x ?y ) bit___true )
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
  (forall
      (?i1 Int ) (?v Int )
    (=
      (word32_array_type___arr_element
        (word32_array_type___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a word32_array_type ) (?s0 Int ) (?t Int )
    (=
      (word32_array_type___arr_element
        (word32_array_type___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a word32_array_type ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (word32_array_type___arr_element
          (word32_array_type___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (word32_array_type___arr_element ?a ?s0p )
      )
    )
  )
  :formula
  (and
    (forall
        (?p_ Int )
      (implies
        (and
          (<= source__index__subtype__1__first ?p_ )
          (<= ?p_ source__index__subtype__1__last )
        )
        (=
          (word32_array_type___arr_element dest ?p_ )
          (word32_array_type___arr_element source ?p_ )
        )
      )
    )
    (forall
        (?p_ Int )
      (implies
        (and
          (<= (+ source__index__subtype__1__last 1 ) ?p_ )
          (<= ?p_ loop__2__i )
        )
        (= (word32_array_type___arr_element dest ?p_ ) 0 )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and
          (<= source__index__subtype__1__first ?i___1 )
          (<= ?i___1 source__index__subtype__1__last )
        )
        (and
          (<= 0 (word32_array_type___arr_element source ?i___1 ) )
          (<=
            (word32_array_type___arr_element source ?i___1 )
            4294967295
          )
        )
      )
    )
    (=
      source__index__subtype__1__first
      dest__index__subtype__1__first
    )
    (<= 0 loop__2__i )
    (<= loop__2__i 79 )
    (<= (+ source__index__subtype__1__last 1 ) loop__2__i )
    (<= dest__index__subtype__1__first loop__2__i )
    (<= (+ loop__2__i 1 ) dest__index__subtype__1__last )
    (<= 0 index__size )
    (<= index__base__first index__base__last )
    (<= 0 word32__size )
    (<=
      source__index__subtype__1__first
      source__index__subtype__1__last
    )
    (<=
      dest__index__subtype__1__first
      dest__index__subtype__1__last
    )
    (<= index__base__first 0 )
    (<= 0 source__index__subtype__1__first )
    (<= 0 source__index__subtype__1__last )
    (<= 0 dest__index__subtype__1__first )
    (<= 0 dest__index__subtype__1__last )
    (<= 79 index__base__last )
    (<= source__index__subtype__1__last 79 )
    (<= source__index__subtype__1__first 79 )
    (<= dest__index__subtype__1__last 79 )
    (<= dest__index__subtype__1__first 79 )
    (not
      (forall
          (?p_ Int )
        (implies
          (and
            (<= source__index__subtype__1__first ?p_ )
            (<= ?p_ source__index__subtype__1__last )
          )
          (=
            (word32_array_type___arr_element
              (word32_array_type___arr_update dest (+ loop__2__i 1 ) 0 )
              ?p_
            )
            (word32_array_type___arr_element source ?p_ )
          )
        )
      )
    )
  )
  :status unknown
)
