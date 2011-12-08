(benchmark lockdoor.3.1
  :logic AUFNIRA
  :extrasorts 
  ( clock__timet
    latch__statetype
    statetype
    real___type
  )
  :extrafuns 
  ( (alarmtimeout clock__timet )
    (alarmtimeout___init clock__timet )
    (alarmtimeout___loopinit clock__timet )
    (alarmtypes__alarming Int )
    (alarmtypes__silent Int )
    (alarmtypes__statust__base__first Int )
    (alarmtypes__statust__base__last Int )
    (alarmtypes__statust__first Int )
    (alarmtypes__statust__last Int )
    (alarmtypes__statust__size Int )
    (bit___false Int )
    (bit___true Int )
    (clock__currenttime clock__timet )
    (clock__currenttime___init clock__timet )
    (clock__currenttime___loopinit clock__timet )
    (closed Int )
    (currentdoor Int )
    (currentdoor___init Int )
    (currentdoor___loopinit Int )
    (dooralarm Int )
    (dooralarm__3 Int )
    (dooralarm__3___init Int )
    (dooralarm__3___loopinit Int )
    (dooralarm___init Int )
    (dooralarm___loopinit Int )
    (latch__state latch__statetype )
    (latch__state__1 latch__statetype )
    (latch__state__1___init latch__statetype )
    (latch__state__1___loopinit latch__statetype )
    (latch__state__2 latch__statetype )
    (latch__state__2___init latch__statetype )
    (latch__state__2___loopinit latch__statetype )
    (latch__state___init latch__statetype )
    (latch__state___loopinit latch__statetype )
    (open Int )
    (state statetype )
    (state___init statetype )
    (state___loopinit statetype )
    (statetype___default_rcd statetype )
    (statetype__size Int )
    (t__base__first Int )
    (t__base__last Int )
    (t__first Int )
    (t__last Int )
    (t__size Int )
    (alarmtypes__statust___bit_eq Int Int Int )
    (alarmtypes__statust__pos Int Int )
    (alarmtypes__statust__pred Int Int )
    (alarmtypes__statust__succ Int Int )
    (alarmtypes__statust__val Int Int )
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
    (clock__thecurrenttime clock__timet clock__timet )
    (clock__timet___bit_eq clock__timet clock__timet Int )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (latch__prf_latchtimeout latch__statetype clock__timet )
    (latch__statetype___bit_eq
      latch__statetype
      latch__statetype
      Int
    )
    (prf_alarmtimeout statetype clock__timet )
    (real___abs real___type real___type )
    (real___bit_eq real___type real___type Int )
    (real___div real___type real___type real___type )
    (real___exp real___type Int real___type )
    (real___minus real___type real___type real___type )
    (real___plus real___type real___type real___type )
    (real___times real___type real___type real___type )
    (real___uminus real___type real___type )
    (round__ real___type Int )
    (statetype___alarmtimeout___rcd_element
      statetype
      clock__timet
    )
    (statetype___alarmtimeout___rcd_update
      statetype
      clock__timet
      statetype
    )
    (statetype___bit_eq statetype statetype Int )
    (statetype___currentdoor___rcd_element statetype Int )
    (statetype___currentdoor___rcd_update
      statetype
      Int
      statetype
    )
    (statetype___dooralarm___rcd_element statetype Int )
    (statetype___dooralarm___rcd_update
      statetype
      Int
      statetype
    )
    (t___bit_eq Int Int Int )
    (t__pos Int Int )
    (t__pred Int Int )
    (t__succ Int Int )
    (t__val Int Int )
    (thecurrentdoor statetype Int )
    (thedooralarm statetype Int )
  )
  :extrapreds 
  ( (alarmtypes__statust__LE Int Int )
    (alarmtypes__statust__LT Int Int )
    (alarmtypes__statust___member Int )
    (bit___type___member Int )
    (clock__greaterthanorequal clock__timet clock__timet )
    (int___odd Int )
    (latch__islocked latch__statetype )
    (real___le real___type real___type )
    (real___lt real___type real___type )
    (statetype___member statetype )
    (t__LE Int Int )
    (t__LT Int Int )
    (t___member Int )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (alarmtypes__statust___member ?i )
      (= (alarmtypes__statust__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (alarmtypes__statust___member ?i )
      (= (alarmtypes__statust__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (alarmtypes__statust___member ?i )
      (implies
        (< ?i 1 )
        (= (alarmtypes__statust__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (alarmtypes__statust___member ?i )
      (implies
        (< 0 ?i )
        (= (alarmtypes__statust__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= alarmtypes__alarming 0 )
  :assumption
  (= alarmtypes__silent 1 )
  :assumption
  (forall
      (?i Int )
    (implies (t___member ?i ) (= (t__pos ?i ) ?i ) )
  )
  :assumption
  (forall
      (?i Int )
    (implies (t___member ?i ) (= (t__val ?i ) ?i ) )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (t___member ?i )
      (implies (< ?i 1 ) (= (t__succ ?i ) (+ ?i 1 ) ) )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (t___member ?i )
      (implies (< 0 ?i ) (= (t__pred ?i ) (- ?i 1 ) ) )
    )
  )
  :assumption
  (= open 0 )
  :assumption
  (= closed 1 )
  :assumption
  (<= 0 alarmtypes__statust__size )
  :assumption
  (= alarmtypes__statust__first alarmtypes__alarming )
  :assumption
  (= alarmtypes__statust__last alarmtypes__silent )
  :assumption
  (= alarmtypes__statust__base__first alarmtypes__alarming )
  :assumption
  (= alarmtypes__statust__base__last alarmtypes__silent )
  :assumption
  (<= 0 t__size )
  :assumption
  (= t__first open )
  :assumption
  (= t__last closed )
  :assumption
  (= t__base__first open )
  :assumption
  (= t__base__last closed )
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
  (alarmtypes__statust___member alarmtypes__alarming )
  :assumption
  (alarmtypes__statust___member alarmtypes__silent )
  :assumption
  (alarmtypes__statust___member
    alarmtypes__statust__base__first
  )
  :assumption
  (alarmtypes__statust___member
    alarmtypes__statust__base__last
  )
  :assumption
  (alarmtypes__statust___member alarmtypes__statust__first )
  :assumption
  (alarmtypes__statust___member alarmtypes__statust__last )
  :assumption
  (t___member closed )
  :assumption
  (t___member currentdoor )
  :assumption
  (t___member currentdoor___init )
  :assumption
  (t___member currentdoor___loopinit )
  :assumption
  (alarmtypes__statust___member dooralarm )
  :assumption
  (alarmtypes__statust___member dooralarm__3 )
  :assumption
  (alarmtypes__statust___member dooralarm__3___init )
  :assumption
  (alarmtypes__statust___member dooralarm__3___loopinit )
  :assumption
  (alarmtypes__statust___member dooralarm___init )
  :assumption
  (alarmtypes__statust___member dooralarm___loopinit )
  :assumption
  (t___member open )
  :assumption
  (statetype___member state )
  :assumption
  (statetype___member state___init )
  :assumption
  (statetype___member state___loopinit )
  :assumption
  (t___member t__base__first )
  :assumption
  (t___member t__base__last )
  :assumption
  (t___member t__first )
  :assumption
  (t___member t__last )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (alarmtypes__statust___member ?x0 )
      (alarmtypes__statust___member
        (alarmtypes__statust__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (alarmtypes__statust___member ?x0 )
      (alarmtypes__statust___member
        (alarmtypes__statust__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (alarmtypes__statust___member
      (alarmtypes__statust__val ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies (t___member ?x0 ) (t___member (t__pred ?x0 ) ) )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies (t___member ?x0 ) (t___member (t__succ ?x0 ) ) )
  )
  :assumption
  (forall   (?x0 Int ) (t___member (t__val ?x0 ) ) )
  :assumption
  (forall
      (?x0 statetype )
    (implies
      (statetype___member ?x0 )
      (t___member (thecurrentdoor ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 statetype )
    (implies
      (statetype___member ?x0 )
      (alarmtypes__statust___member (thedooralarm ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (alarmtypes__statust___member ?x )
      (and (<= 0 ?x ) (<= ?x 1 ) )
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
      (?x statetype )
    (iff
      (statetype___member ?x )
      (and
        (alarmtypes__statust___member
          (statetype___dooralarm___rcd_element ?x )
        )
        true
        (t___member (statetype___currentdoor___rcd_element ?x ) )
      )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff (t___member ?x ) (and (<= 0 ?x ) (<= ?x 1 ) ) )
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
    (iff
      (= (alarmtypes__statust___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x clock__timet ) (?y clock__timet )
    (iff
      (= (clock__timet___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x latch__statetype ) (?y latch__statetype )
    (iff
      (= (latch__statetype___bit_eq ?x ?y ) bit___true )
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
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___dooralarm___rcd_element
        (statetype___dooralarm___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t clock__timet )
    (=
      (statetype___dooralarm___rcd_element
        (statetype___alarmtimeout___rcd_update ?r ?t )
      )
      (statetype___dooralarm___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___dooralarm___rcd_element
        (statetype___currentdoor___rcd_update ?r ?t )
      )
      (statetype___dooralarm___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___alarmtimeout___rcd_element
        (statetype___dooralarm___rcd_update ?r ?t )
      )
      (statetype___alarmtimeout___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t clock__timet )
    (=
      (statetype___alarmtimeout___rcd_element
        (statetype___alarmtimeout___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___alarmtimeout___rcd_element
        (statetype___currentdoor___rcd_update ?r ?t )
      )
      (statetype___alarmtimeout___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___currentdoor___rcd_element
        (statetype___dooralarm___rcd_update ?r ?t )
      )
      (statetype___currentdoor___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t clock__timet )
    (=
      (statetype___currentdoor___rcd_element
        (statetype___alarmtimeout___rcd_update ?r ?t )
      )
      (statetype___currentdoor___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___currentdoor___rcd_element
        (statetype___currentdoor___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (<= open currentdoor )
    (<= currentdoor closed )
    (<= alarmtypes__alarming dooralarm )
    (<= dooralarm alarmtypes__silent )
    (=
      (latch__prf_latchtimeout latch__state__1 )
      (clock__thecurrenttime clock__currenttime )
    )
    (iff
      (latch__islocked latch__state__2 )
      (clock__greaterthanorequal
        (clock__thecurrenttime clock__currenttime )
        (latch__prf_latchtimeout latch__state__2 )
      )
    )
    (=
      (latch__prf_latchtimeout latch__state__2 )
      (latch__prf_latchtimeout latch__state__1 )
    )
    (=
      (latch__prf_latchtimeout latch__state__2 )
      (clock__thecurrenttime clock__currenttime )
    )
    (iff
      (and
        (= currentdoor open )
        (and
          (latch__islocked latch__state__2 )
          (clock__greaterthanorequal
            (clock__thecurrenttime clock__currenttime )
            (clock__thecurrenttime clock__currenttime )
          )
        )
      )
      (= dooralarm__3 alarmtypes__alarming )
    )
    (<= alarmtypes__alarming dooralarm__3 )
    (<= dooralarm__3 alarmtypes__silent )
    (clock__greaterthanorequal
      (clock__thecurrenttime clock__currenttime )
      (clock__thecurrenttime clock__currenttime )
    )
    (<= 0 alarmtypes__statust__size )
    (<= 0 t__size )
    (not (latch__islocked latch__state__2 ) )
  )
  :status unknown
)
