(benchmark enrolop.9.1
  :logic AUFNIRA
  :extrasorts ( keystore__state__type statetype real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (enclavequiescent Int )
    (enrolmentstates__base__first Int )
    (enrolmentstates__base__last Int )
    (enrolmentstates__first Int )
    (enrolmentstates__last Int )
    (enrolmentstates__size Int )
    (gotadmintoken Int )
    (keystore__state keystore__state__type )
    (keystore__state__2 keystore__state__type )
    (keystore__state__2___init keystore__state__type )
    (keystore__state__2___loopinit keystore__state__type )
    (keystore__state___init keystore__state__type )
    (keystore__state___loopinit keystore__state__type )
    (notenrolled Int )
    (shutdown Int )
    (state statetype )
    (state___init statetype )
    (state___loopinit statetype )
    (statetype___default_rcd statetype )
    (statetype__size Int )
    (status' Int )
    (status__1 Int )
    (status__1___init Int )
    (status__1___loopinit Int )
    (status__2 Int )
    (status__2___init Int )
    (status__2___loopinit Int )
    (status__3 Int )
    (status__3___init Int )
    (status__3___loopinit Int )
    (status___init Int )
    (status___loopinit Int )
    (statust__base__first Int )
    (statust__base__last Int )
    (statust__first Int )
    (statust__last Int )
    (statust__size Int )
    (waitingendenrol Int )
    (waitingenrol Int )
    (waitingfinishadminop Int )
    (waitingremoveadmintokenfail Int )
    (waitingstartadminop Int )
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
    (keystore__state__type___bit_eq
      keystore__state__type
      keystore__state__type
      Int
    )
    (real___abs real___type real___type )
    (real___bit_eq real___type real___type Int )
    (real___div real___type real___type real___type )
    (real___exp real___type Int real___type )
    (real___minus real___type real___type real___type )
    (real___plus real___type real___type real___type )
    (real___times real___type real___type real___type )
    (real___uminus real___type real___type )
    (round__ real___type Int )
    (statetype___bit_eq statetype statetype Int )
    (statetype___status___rcd_element statetype Int )
    (statetype___status___rcd_update statetype Int statetype )
    (statust___bit_eq Int Int Int )
    (statust__pos Int Int )
    (statust__pred Int Int )
    (statust__succ Int Int )
    (statust__val Int Int )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (enclave__enrolmentisinprogress statetype )
    (enrolmentisinprogress Int )
    (int___odd Int )
    (keystore__privatekeypresent keystore__state__type )
    (prf_statusisenclavequiescent statetype )
    (real___le real___type real___type )
    (real___lt real___type real___type )
    (statetype___member statetype )
    (statust__LE Int Int )
    (statust__LT Int Int )
    (statust___member Int )
  )
  :assumption
  (forall
      (?i Int )
    (implies (statust___member ?i ) (= (statust__pos ?i ) ?i ) )
  )
  :assumption
  (forall
      (?i Int )
    (implies (statust___member ?i ) (= (statust__val ?i ) ?i ) )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (statust___member ?i )
      (implies (< ?i 8 ) (= (statust__succ ?i ) (+ ?i 1 ) ) )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (statust___member ?i )
      (implies (< 0 ?i ) (= (statust__pred ?i ) (- ?i 1 ) ) )
    )
  )
  :assumption
  (= notenrolled 0 )
  :assumption
  (= waitingenrol 1 )
  :assumption
  (= waitingendenrol 2 )
  :assumption
  (= enclavequiescent 3 )
  :assumption
  (= waitingremoveadmintokenfail 4 )
  :assumption
  (= gotadmintoken 5 )
  :assumption
  (= waitingstartadminop 6 )
  :assumption
  (= waitingfinishadminop 7 )
  :assumption
  (= shutdown 8 )
  :assumption
  (<= 0 statust__size )
  :assumption
  (= statust__first notenrolled )
  :assumption
  (= statust__last shutdown )
  :assumption
  (= statust__base__first notenrolled )
  :assumption
  (= statust__base__last shutdown )
  :assumption
  (<= 0 enrolmentstates__size )
  :assumption
  (= enrolmentstates__first notenrolled )
  :assumption
  (= enrolmentstates__last waitingendenrol )
  :assumption
  (= enrolmentstates__base__first notenrolled )
  :assumption
  (= enrolmentstates__base__last shutdown )
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
  (statust___member enclavequiescent )
  :assumption
  (statust___member enrolmentstates__base__first )
  :assumption
  (statust___member enrolmentstates__base__last )
  :assumption
  (statust___member enrolmentstates__first )
  :assumption
  (statust___member enrolmentstates__last )
  :assumption
  (statust___member gotadmintoken )
  :assumption
  (statust___member notenrolled )
  :assumption
  (statust___member shutdown )
  :assumption
  (statetype___member state )
  :assumption
  (statetype___member state___init )
  :assumption
  (statetype___member state___loopinit )
  :assumption
  (statust___member status' )
  :assumption
  (statust___member status__1 )
  :assumption
  (statust___member status__1___init )
  :assumption
  (statust___member status__1___loopinit )
  :assumption
  (statust___member status__2 )
  :assumption
  (statust___member status__2___init )
  :assumption
  (statust___member status__2___loopinit )
  :assumption
  (statust___member status__3 )
  :assumption
  (statust___member status__3___init )
  :assumption
  (statust___member status__3___loopinit )
  :assumption
  (statust___member status___init )
  :assumption
  (statust___member status___loopinit )
  :assumption
  (statust___member statust__base__first )
  :assumption
  (statust___member statust__base__last )
  :assumption
  (statust___member statust__first )
  :assumption
  (statust___member statust__last )
  :assumption
  (statust___member waitingendenrol )
  :assumption
  (statust___member waitingenrol )
  :assumption
  (statust___member waitingfinishadminop )
  :assumption
  (statust___member waitingremoveadmintokenfail )
  :assumption
  (statust___member waitingstartadminop )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (statust___member ?x0 )
      (statust___member (statust__pred ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (statust___member ?x0 )
      (statust___member (statust__succ ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (statust___member (statust__val ?x0 ) )
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
      (?x statetype )
    (iff
      (statetype___member ?x )
      (statust___member (statetype___status___rcd_element ?x ) )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff (statust___member ?x ) (and (<= 0 ?x ) (<= ?x 8 ) ) )
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
      (?x keystore__state__type ) (?y keystore__state__type )
    (iff
      (= (keystore__state__type___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x statetype ) (?y statetype )
    (iff
      (= (statetype___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff (= (statust___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
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
      (?r statetype ) (?t Int )
    (=
      (statetype___status___rcd_element
        (statetype___status___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (enrolmentisinprogress waitingenrol )
    (not (keystore__privatekeypresent keystore__state ) )
    (or
      (and
        (= status__2 enclavequiescent )
        (keystore__privatekeypresent keystore__state__2 )
      )
      (and
        (= status__2 waitingendenrol )
        (not (keystore__privatekeypresent keystore__state__2 ) )
      )
    )
    (<= notenrolled status__2 )
    (<= status__2 shutdown )
    (iff
      (enrolmentisinprogress status__2 )
      (and
        (<= notenrolled status__2 )
        (<= status__2 waitingendenrol )
      )
    )
    (<= 0 statust__size )
    (<= 0 enrolmentstates__size )
    (not
      (iff
        (keystore__privatekeypresent keystore__state__2 )
        (not (enrolmentisinprogress status__2 ) )
      )
    )
  )
  :status unknown
)
