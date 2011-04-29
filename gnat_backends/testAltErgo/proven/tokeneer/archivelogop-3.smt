(benchmark archivelogop.3.1
  :logic AUFNIRA
  :extrasorts ( admin__t admintoken__statetype real___type )
  :extrafuns 
  ( (admin__archivelog Int )
    (admin__nullop Int )
    (admin__opandnullt__base__first Int )
    (admin__opandnullt__base__last Int )
    (admin__opandnullt__first Int )
    (admin__opandnullt__last Int )
    (admin__opandnullt__size Int )
    (admin__overridelock Int )
    (admin__shutdownop Int )
    (admin__updateconfigdata Int )
    (admintoken__state admintoken__statetype )
    (admintoken__state___init admintoken__statetype )
    (admintoken__state___loopinit admintoken__statetype )
    (bit___false Int )
    (bit___true Int )
    (enclavequiescent Int )
    (gotadmintoken Int )
    (notenrolled Int )
    (privtypes__auditmanager Int )
    (privtypes__guard Int )
    (privtypes__privileget__base__first Int )
    (privtypes__privileget__base__last Int )
    (privtypes__privileget__first Int )
    (privtypes__privileget__last Int )
    (privtypes__privileget__size Int )
    (privtypes__securityofficer Int )
    (privtypes__useronly Int )
    (shutdown Int )
    (status' Int )
    (status__1 Int )
    (status__1___init Int )
    (status__1___loopinit Int )
    (status__2 Int )
    (status__2___init Int )
    (status__2___loopinit Int )
    (status___init Int )
    (status___loopinit Int )
    (statust__base__first Int )
    (statust__base__last Int )
    (statust__first Int )
    (statust__last Int )
    (statust__size Int )
    (theadmin admin__t )
    (theadmin__2 admin__t )
    (theadmin__2___init admin__t )
    (theadmin__2___loopinit admin__t )
    (theadmin___init admin__t )
    (theadmin___loopinit admin__t )
    (waitingendenrol Int )
    (waitingenrol Int )
    (waitingfinishadminop Int )
    (waitingremoveadmintokenfail Int )
    (waitingstartadminop Int )
    (admin__opandnullt___bit_eq Int Int Int )
    (admin__opandnullt__pos Int Int )
    (admin__opandnullt__pred Int Int )
    (admin__opandnullt__succ Int Int )
    (admin__opandnullt__val Int Int )
    (admin__prf_rolepresent admin__t Int )
    (admin__t___bit_eq admin__t admin__t Int )
    (admin__thecurrentop admin__t Int )
    (admintoken__statetype___bit_eq
      admintoken__statetype
      admintoken__statetype
      Int
    )
    (admintoken__theauthcertrole admintoken__statetype Int )
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
    (privtypes__privileget___bit_eq Int Int Int )
    (privtypes__privileget__pos Int Int )
    (privtypes__privileget__pred Int Int )
    (privtypes__privileget__succ Int Int )
    (privtypes__privileget__val Int Int )
    (real___abs real___type real___type )
    (real___bit_eq real___type real___type Int )
    (real___div real___type real___type real___type )
    (real___exp real___type Int real___type )
    (real___minus real___type real___type real___type )
    (real___plus real___type real___type real___type )
    (real___times real___type real___type real___type )
    (real___uminus real___type real___type )
    (round__ real___type Int )
    (statust___bit_eq Int Int Int )
    (statust__pos Int Int )
    (statust__pred Int Int )
    (statust__succ Int Int )
    (statust__val Int Int )
  )
  :extrapreds 
  ( (admin__isdoingop admin__t )
    (admin__ispresent admin__t )
    (admin__opandnullt__LE Int Int )
    (admin__opandnullt__LT Int Int )
    (admin__opandnullt___member Int )
    (admintoken__prf_authcertvalid admintoken__statetype )
    (admintoken__prf_isgood admintoken__statetype )
    (bit___type___member Int )
    (int___odd Int )
    (privtypes__privileget__LE Int Int )
    (privtypes__privileget__LT Int Int )
    (privtypes__privileget___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
    (statust__LE Int Int )
    (statust__LT Int Int )
    (statust___member Int )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (privtypes__privileget___member ?i )
      (= (privtypes__privileget__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (privtypes__privileget___member ?i )
      (= (privtypes__privileget__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (privtypes__privileget___member ?i )
      (implies
        (< ?i 3 )
        (= (privtypes__privileget__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (privtypes__privileget___member ?i )
      (implies
        (< 0 ?i )
        (= (privtypes__privileget__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= privtypes__useronly 0 )
  :assumption
  (= privtypes__guard 1 )
  :assumption
  (= privtypes__auditmanager 2 )
  :assumption
  (= privtypes__securityofficer 3 )
  :assumption
  (forall
      (?i Int )
    (implies
      (admin__opandnullt___member ?i )
      (= (admin__opandnullt__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (admin__opandnullt___member ?i )
      (= (admin__opandnullt__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (admin__opandnullt___member ?i )
      (implies
        (< ?i 4 )
        (= (admin__opandnullt__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (admin__opandnullt___member ?i )
      (implies
        (< 0 ?i )
        (= (admin__opandnullt__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= admin__nullop 0 )
  :assumption
  (= admin__archivelog 1 )
  :assumption
  (= admin__updateconfigdata 2 )
  :assumption
  (= admin__overridelock 3 )
  :assumption
  (= admin__shutdownop 4 )
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
  (<= 0 privtypes__privileget__size )
  :assumption
  (= privtypes__privileget__first privtypes__useronly )
  :assumption
  (= privtypes__privileget__last privtypes__securityofficer )
  :assumption
  (= privtypes__privileget__base__first privtypes__useronly )
  :assumption
  (=
    privtypes__privileget__base__last
    privtypes__securityofficer
  )
  :assumption
  (<= 0 admin__opandnullt__size )
  :assumption
  (= admin__opandnullt__first admin__nullop )
  :assumption
  (= admin__opandnullt__last admin__shutdownop )
  :assumption
  (= admin__opandnullt__base__first admin__nullop )
  :assumption
  (= admin__opandnullt__base__last admin__shutdownop )
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
  (admin__opandnullt___member admin__archivelog )
  :assumption
  (admin__opandnullt___member admin__nullop )
  :assumption
  (admin__opandnullt___member admin__opandnullt__base__first )
  :assumption
  (admin__opandnullt___member admin__opandnullt__base__last )
  :assumption
  (admin__opandnullt___member admin__opandnullt__first )
  :assumption
  (admin__opandnullt___member admin__opandnullt__last )
  :assumption
  (admin__opandnullt___member admin__overridelock )
  :assumption
  (admin__opandnullt___member admin__shutdownop )
  :assumption
  (admin__opandnullt___member admin__updateconfigdata )
  :assumption
  (statust___member enclavequiescent )
  :assumption
  (statust___member gotadmintoken )
  :assumption
  (statust___member notenrolled )
  :assumption
  (privtypes__privileget___member privtypes__auditmanager )
  :assumption
  (privtypes__privileget___member privtypes__guard )
  :assumption
  (privtypes__privileget___member
    privtypes__privileget__base__first
  )
  :assumption
  (privtypes__privileget___member
    privtypes__privileget__base__last
  )
  :assumption
  (privtypes__privileget___member
    privtypes__privileget__first
  )
  :assumption
  (privtypes__privileget___member
    privtypes__privileget__last
  )
  :assumption
  (privtypes__privileget___member privtypes__securityofficer )
  :assumption
  (privtypes__privileget___member privtypes__useronly )
  :assumption
  (statust___member shutdown )
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
      (admin__opandnullt___member ?x0 )
      (admin__opandnullt___member (admin__opandnullt__pred ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (admin__opandnullt___member ?x0 )
      (admin__opandnullt___member (admin__opandnullt__succ ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (admin__opandnullt___member (admin__opandnullt__val ?x0 ) )
  )
  :assumption
  (forall
      (?x0 admin__t )
    (privtypes__privileget___member
      (admin__prf_rolepresent ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 admin__t )
    (admin__opandnullt___member (admin__thecurrentop ?x0 ) )
  )
  :assumption
  (forall
      (?x0 admintoken__statetype )
    (privtypes__privileget___member
      (admintoken__theauthcertrole ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (privtypes__privileget___member ?x0 )
      (privtypes__privileget___member
        (privtypes__privileget__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (privtypes__privileget___member ?x0 )
      (privtypes__privileget___member
        (privtypes__privileget__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (privtypes__privileget___member
      (privtypes__privileget__val ?x0 )
    )
  )
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
      (admin__opandnullt___member ?x )
      (and (<= 0 ?x ) (<= ?x 4 ) )
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
      (?x Int )
    (iff
      (privtypes__privileget___member ?x )
      (and (<= 0 ?x ) (<= ?x 3 ) )
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
      (?x Int ) (?y Int )
    (iff
      (= (admin__opandnullt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x admin__t ) (?y admin__t )
    (iff (= (admin__t___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x admintoken__statetype ) (?y admintoken__statetype )
    (iff
      (= (admintoken__statetype___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (privtypes__privileget___bit_eq ?x ?y ) bit___true )
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
  :formula
  (and
    (admin__ispresent theadmin )
    (admin__isdoingop theadmin )
    (= (admin__thecurrentop theadmin ) admin__archivelog )
    (implies
      (= (admin__prf_rolepresent theadmin ) privtypes__guard )
      (and
        (admintoken__prf_isgood admintoken__state )
        (and
          (admintoken__prf_authcertvalid admintoken__state )
          (=
            (admintoken__theauthcertrole admintoken__state )
            privtypes__guard
          )
        )
      )
    )
    (implies
      (and
        (admin__isdoingop theadmin )
        (= (admin__thecurrentop theadmin ) admin__overridelock )
      )
      (= (admin__prf_rolepresent theadmin ) privtypes__guard )
    )
    (implies
      (= (admin__prf_rolepresent theadmin ) privtypes__guard )
      (or
        (and
          (admin__isdoingop theadmin )
          (= (admin__thecurrentop theadmin ) admin__overridelock )
        )
        (not (admin__isdoingop theadmin ) )
      )
    )
    (or
      (= status__1 waitingstartadminop )
      (= status__1 waitingfinishadminop )
    )
    (<= notenrolled status__1 )
    (<= status__1 shutdown )
    (<= 0 privtypes__privileget__size )
    (<= 0 admin__opandnullt__size )
    (<= 0 statust__size )
    (not
      (or
        (= status__1 waitingstartadminop )
        (or
          (= status__1 waitingfinishadminop )
          (= status__1 enclavequiescent )
        )
      )
    )
  )
  :status unknown
)
