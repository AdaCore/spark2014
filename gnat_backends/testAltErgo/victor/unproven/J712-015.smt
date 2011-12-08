(benchmark short_div6.1.1
  :logic AUFNIRA
  :extrasorts ( mod_types big_unsigned real___type )
  :extrafuns 
  ( (big_unsigned___default_rcd big_unsigned )
    (big_unsigned__size Int )
    (big_unsigned_zero big_unsigned )
    (bit___false Int )
    (bit___true Int )
    (carry Int )
    (carry___init Int )
    (carry___loopinit Int )
    (dividend big_unsigned )
    (dividend___init big_unsigned )
    (dividend___loopinit big_unsigned )
    (divisor Int )
    (divisor___init Int )
    (divisor___loopinit Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (interfaces__unsigned_64__base__first Int )
    (interfaces__unsigned_64__base__last Int )
    (interfaces__unsigned_64__first Int )
    (interfaces__unsigned_64__last Int )
    (interfaces__unsigned_64__modulus Int )
    (interfaces__unsigned_64__size Int )
    (largest_unsigned__base__first Int )
    (largest_unsigned__base__last Int )
    (largest_unsigned__first Int )
    (largest_unsigned__last Int )
    (largest_unsigned__modulus Int )
    (largest_unsigned__size Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (mod_index__base__first Int )
    (mod_index__base__last Int )
    (mod_index__first Int )
    (mod_index__last Int )
    (mod_index__size Int )
    (mod_type__base__first Int )
    (mod_type__base__last Int )
    (mod_type__first Int )
    (mod_type__last Int )
    (mod_type__modulus Int )
    (mod_type__size Int )
    (mod_types___default_arr mod_types )
    (mod_types___default_arr_element Int )
    (natural__base__first Int )
    (natural__base__last Int )
    (natural__first Int )
    (natural__last Int )
    (natural__size Int )
    (temp_quotient big_unsigned )
    (temp_quotient___init big_unsigned )
    (temp_quotient___loopinit big_unsigned )
    (big_unsigned___bit_eq big_unsigned big_unsigned Int )
    (big_unsigned___data___rcd_element big_unsigned mod_types )
    (big_unsigned___data___rcd_update
      big_unsigned
      mod_types
      big_unsigned
    )
    (big_unsigned___last_index___rcd_element big_unsigned Int )
    (big_unsigned___last_index___rcd_update
      big_unsigned
      Int
      big_unsigned
    )
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
    (interfaces__unsigned_64___bit_eq Int Int Int )
    (largest_unsigned___bit_eq Int Int Int )
    (mod_type___bit_eq Int Int Int )
    (mod_types___arr_element mod_types Int Int )
    (mod_types___arr_update mod_types Int Int mod_types )
    (mod_types___bit_eq mod_types mod_types Int )
    (mod_types___mk_const_arr Int mod_types )
    (real___abs real___type real___type )
    (real___bit_eq real___type real___type Int )
    (real___div real___type real___type real___type )
    (real___exp real___type Int real___type )
    (real___minus real___type real___type real___type )
    (real___plus real___type real___type real___type )
    (real___times real___type real___type real___type )
    (real___uminus real___type real___type )
    (round__ real___type Int )
    (sr__shift_left_64 Int Int Int )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (equal_mod big_unsigned Int )
    (int___odd Int )
    (less_than_mod big_unsigned Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (<=
    mod_index__first
    (big_unsigned___last_index___rcd_element big_unsigned_zero )
  )
  :assumption
  (<=
    (big_unsigned___last_index___rcd_element big_unsigned_zero )
    mod_index__last
  )
  :assumption
  (forall
      (?I Int )
    (implies
      (and (<= 0 ?I ) (<= ?I 31 ) )
      (<=
        mod_type__first
        (mod_types___arr_element
          (big_unsigned___data___rcd_element big_unsigned_zero )
          ?I
        )
      )
    )
  )
  :assumption
  (forall
      (?I Int )
    (implies
      (and (<= 0 ?I ) (<= ?I 31 ) )
      (<=
        (mod_types___arr_element
          (big_unsigned___data___rcd_element big_unsigned_zero )
          ?I
        )
        mod_type__last
      )
    )
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
  (<= 0 natural__size )
  :assumption
  (= natural__first 0 )
  :assumption
  (= natural__last 2147483647 )
  :assumption
  (= natural__base__first (~ 2147483648 ) )
  :assumption
  (= natural__base__last 2147483647 )
  :assumption
  (<= 0 interfaces__unsigned_64__size )
  :assumption
  (= interfaces__unsigned_64__first 0 )
  :assumption
  (= interfaces__unsigned_64__last 18446744073709551615 )
  :assumption
  (= interfaces__unsigned_64__base__first 0 )
  :assumption
  (=
    interfaces__unsigned_64__base__last
    18446744073709551615
  )
  :assumption
  (= interfaces__unsigned_64__modulus 18446744073709551616 )
  :assumption
  (<= 0 mod_index__size )
  :assumption
  (= mod_index__first 0 )
  :assumption
  (= mod_index__last 31 )
  :assumption
  (= mod_index__base__first (~ 2147483648 ) )
  :assumption
  (= mod_index__base__last 2147483647 )
  :assumption
  (<= 0 mod_type__size )
  :assumption
  (= mod_type__size 32 )
  :assumption
  (= mod_type__first 0 )
  :assumption
  (= mod_type__last 4294967295 )
  :assumption
  (= mod_type__base__first 0 )
  :assumption
  (= mod_type__base__last 4294967295 )
  :assumption
  (= mod_type__modulus 4294967296 )
  :assumption
  (<= 0 big_unsigned__size )
  :assumption
  (forall
      (?A big_unsigned ) (?B big_unsigned )
    (implies
      (and
        (=
          (big_unsigned___last_index___rcd_element ?A )
          (big_unsigned___last_index___rcd_element ?B )
        )
        (=
          (big_unsigned___data___rcd_element ?A )
          (big_unsigned___data___rcd_element ?B )
        )
      )
      (= ?A ?B )
    )
  )
  :assumption
  (<= 0 largest_unsigned__size )
  :assumption
  (= largest_unsigned__first 0 )
  :assumption
  (= largest_unsigned__last 18446744073709551615 )
  :assumption
  (= largest_unsigned__base__first 0 )
  :assumption
  (= largest_unsigned__base__last 18446744073709551615 )
  :assumption
  (= largest_unsigned__modulus 18446744073709551616 )
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
      (?x big_unsigned ) (?y big_unsigned )
    (iff
      (= (big_unsigned___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (interfaces__unsigned_64___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (largest_unsigned___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff (= (mod_type___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x mod_types ) (?y mod_types )
    (iff
      (= (mod_types___bit_eq ?x ?y ) bit___true )
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
      (mod_types___arr_element
        (mod_types___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a mod_types ) (?s0 Int ) (?t Int )
    (=
      (mod_types___arr_element
        (mod_types___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a mod_types ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (mod_types___arr_element
          (mod_types___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (mod_types___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?r big_unsigned ) (?t Int )
    (=
      (big_unsigned___last_index___rcd_element
        (big_unsigned___last_index___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r big_unsigned ) (?t mod_types )
    (=
      (big_unsigned___last_index___rcd_element
        (big_unsigned___data___rcd_update ?r ?t )
      )
      (big_unsigned___last_index___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r big_unsigned ) (?t Int )
    (=
      (big_unsigned___data___rcd_element
        (big_unsigned___last_index___rcd_update ?r ?t )
      )
      (big_unsigned___data___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r big_unsigned ) (?t mod_types )
    (=
      (big_unsigned___data___rcd_element
        (big_unsigned___data___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (< carry divisor )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 0 ?i___1 ) (<= ?i___1 31 ) )
        (and
          (<=
            0
            (mod_types___arr_element
              (big_unsigned___data___rcd_element dividend )
              ?i___1
            )
          )
          (<=
            (mod_types___arr_element
              (big_unsigned___data___rcd_element dividend )
              ?i___1
            )
            4294967295
          )
        )
      )
    )
    (<= 0 (big_unsigned___last_index___rcd_element dividend ) )
    (<= (big_unsigned___last_index___rcd_element dividend ) 31 )
    (<= divisor 4294967295 )
    (<= 0 loop__1__i )
    (<= loop__1__i 31 )
    (<=
      loop__1__i
      (big_unsigned___last_index___rcd_element dividend )
    )
    (<= 0 carry )
    (<=
      0
      (mod_types___arr_element
        (big_unsigned___data___rcd_element dividend )
        loop__1__i
      )
    )
    (<=
      (mod_types___arr_element
        (big_unsigned___data___rcd_element dividend )
        loop__1__i
      )
      18446744073709551615
    )
    (<= 0 (sr__shift_left_64 carry 32 ) )
    (= (sr__shift_left_64 carry 32 ) (* carry 4294967296 ) )
    (<=
      0
      (+
        (mod_types___arr_element
          (big_unsigned___data___rcd_element dividend )
          loop__1__i
        )
        (sr__shift_left_64 carry 32 )
      )
    )
    (<=
      (+
        (mod_types___arr_element
          (big_unsigned___data___rcd_element dividend )
          loop__1__i
        )
        (sr__shift_left_64 carry 32 )
      )
      18446744073709551615
    )
    (< (sr__shift_left_64 carry 32 ) 18446744069414584320 )
    (<
      (+
        (mod_types___arr_element
          (big_unsigned___data___rcd_element dividend )
          loop__1__i
        )
        (sr__shift_left_64 carry 32 )
      )
      18446744073709551616
    )
    (< 0 divisor )
    (<= 0 integer__size )
    (<= 0 natural__size )
    (<= 0 interfaces__unsigned_64__size )
    (<= 0 mod_index__size )
    (<= 0 big_unsigned__size )
    (<= 0 largest_unsigned__size )
    (<=
      0
      (big_unsigned___last_index___rcd_element big_unsigned_zero )
    )
    (<=
      (big_unsigned___last_index___rcd_element big_unsigned_zero )
      31
    )
    (not
      (<=
        (int___div
          (+
            (mod_types___arr_element
              (big_unsigned___data___rcd_element dividend )
              loop__1__i
            )
            (sr__shift_left_64 carry 32 )
          )
          divisor
        )
        4294967295
      )
    )
  )
  :status unknown
)
