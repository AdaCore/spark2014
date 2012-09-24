(benchmark ispositive_wrong.1
  :logic AUFNIRA
  :extrasorts ( t bit___type real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (t__base__first Int )
    (t__base__last Int )
    (t__first Int )
    (t__last Int )
    (t__size Int )
    (x Int )
    (x___init Int )
    (x___loopinit Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (bit__and Int Int Int )
    (bit__not Int Int Int )
    (bit__or Int Int Int )
    (bit__xor Int Int Int )
    (boolean__pos Int Int )
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
    (real___abs real___type real___type )
    (real___bit_eq real___type real___type Int )
    (real___div real___type real___type real___type )
    (real___exp real___type Int real___type )
    (real___minus real___type real___type real___type )
    (real___plus real___type real___type real___type )
    (real___times real___type real___type real___type )
    (real___uminus real___type real___type )
    (round__ real___type Int )
    (t___bit_eq Int Int Int )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (boolean__val Int )
    (int___odd Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
    (riposte__ce Int )
  )
  :assumption
  (forall
      (?E Int )
    (implies
      (bit___type___member ?E )
      (iff (riposte__ce ?E ) true )
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
  (<= 0 t__size )
  :assumption
  (= t__first (~ 4294967297 ) )
  :assumption
  (= t__last 4294967294 )
  :assumption
  (<= t__base__first t__base__last )
  :assumption
  (<= t__base__first t__first )
  :assumption
  (<= t__last t__base__last )
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
    (iff (= (t___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
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
  (<= integer__first x )
  :assumption
  (<= x integer__last )
  :formula
  (not
    (implies
      (<= 0 x )
      (= (- x (int___div (- (* 2 x ) 1 ) 2 ) ) 0 )
    )
  )
  :status unknown
)
