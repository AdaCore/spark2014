(benchmark opisavailable.7.1
  :logic AUFNIRA
  :extrasorts 
  ( string
    t
    availopst
    keyboard__datat
    privtoavailopst
    datat
    optokeyedt
    real___type
  )
  :extrafuns 
  ( (archivelog Int )
    (availopst___default_arr availopst )
    (availopst___default_arr_element Int )
    (bit___false Int )
    (bit___true Int )
    (character__base__first Int )
    (character__base__last Int )
    (character__first Int )
    (character__last Int )
    (character__size Int )
    (datai__base__first Int )
    (datai__base__last Int )
    (datai__first Int )
    (datai__last Int )
    (datai__size Int )
    (datalengtht__base__first Int )
    (datalengtht__base__last Int )
    (datalengtht__first Int )
    (datalengtht__last Int )
    (datalengtht__size Int )
    (datat___default_rcd datat )
    (datat__size Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (isavailable privtoavailopst )
    (keyboard__datai__base__first Int )
    (keyboard__datai__base__last Int )
    (keyboard__datai__first Int )
    (keyboard__datai__last Int )
    (keyboard__datai__size Int )
    (keyboard__datalengtht__base__first Int )
    (keyboard__datalengtht__base__last Int )
    (keyboard__datalengtht__first Int )
    (keyboard__datalengtht__last Int )
    (keyboard__datalengtht__size Int )
    (keyboard__datat___default_rcd keyboard__datat )
    (keyboard__datat__size Int )
    (keyedop keyboard__datat )
    (keyedop___init keyboard__datat )
    (keyedop___loopinit keyboard__datat )
    (keyedop__entry__loop__2 keyboard__datat )
    (keyedop__entry__loop__2___init keyboard__datat )
    (keyedop__entry__loop__2___loopinit keyboard__datat )
    (loop__1__op Int )
    (loop__1__op___init Int )
    (loop__1__op___loopinit Int )
    (loop__2__i Int )
    (loop__2__i___init Int )
    (loop__2__i___loopinit Int )
    (null__string string )
    (nullop Int )
    (opandnullt__base__first Int )
    (opandnullt__base__last Int )
    (opandnullt__first Int )
    (opandnullt__last Int )
    (opandnullt__size Int )
    (opt__base__first Int )
    (opt__base__last Int )
    (opt__first Int )
    (opt__last Int )
    (opt__size Int )
    (optokeyed optokeyedt )
    (optokeyedt___default_arr optokeyedt )
    (optokeyedt___default_arr_element datat )
    (overridelock Int )
    (positive__base__first Int )
    (positive__base__last Int )
    (positive__first Int )
    (positive__last Int )
    (positive__size Int )
    (privtoavailopst___default_arr privtoavailopst )
    (privtoavailopst___default_arr_element availopst )
    (privtypes__adminprivileget__base__first Int )
    (privtypes__adminprivileget__base__last Int )
    (privtypes__adminprivileget__first Int )
    (privtypes__adminprivileget__last Int )
    (privtypes__adminprivileget__size Int )
    (privtypes__auditmanager Int )
    (privtypes__guard Int )
    (privtypes__privileget__base__first Int )
    (privtypes__privileget__base__last Int )
    (privtypes__privileget__first Int )
    (privtypes__privileget__last Int )
    (privtypes__privileget__size Int )
    (privtypes__securityofficer Int )
    (privtypes__useronly Int )
    (shutdownop Int )
    (string___default_arr string )
    (string___default_arr_element Int )
    (t___default_rcd t )
    (t__size Int )
    (theadmin t )
    (theadmin___init t )
    (theadmin___loopinit t )
    (theop Int )
    (theop___init Int )
    (theop___loopinit Int )
    (updateconfigdata Int )
    (availopst___arr_element availopst Int Int )
    (availopst___arr_update availopst Int Int availopst )
    (availopst___bit_eq availopst availopst Int )
    (availopst___mk_const_arr Int availopst )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (bit__and Int Int Int )
    (bit__not Int Int Int )
    (bit__or Int Int Int )
    (bit__xor Int Int Int )
    (character___bit_eq Int Int Int )
    (character__pos Int Int )
    (character__val Int Int )
    (datat___bit_eq datat datat Int )
    (datat___length___rcd_element datat Int )
    (datat___length___rcd_update datat Int datat )
    (datat___minmatchlength___rcd_element datat Int )
    (datat___minmatchlength___rcd_update datat Int datat )
    (datat___text___rcd_element datat string )
    (datat___text___rcd_update datat string datat )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (keyboard__datat___bit_eq
      keyboard__datat
      keyboard__datat
      Int
    )
    (keyboard__datat___length___rcd_element
      keyboard__datat
      Int
    )
    (keyboard__datat___length___rcd_update
      keyboard__datat
      Int
      keyboard__datat
    )
    (keyboard__datat___text___rcd_element
      keyboard__datat
      string
    )
    (keyboard__datat___text___rcd_update
      keyboard__datat
      string
      keyboard__datat
    )
    (opandnullt___bit_eq Int Int Int )
    (opandnullt__pos Int Int )
    (opandnullt__pred Int Int )
    (opandnullt__succ Int Int )
    (opandnullt__val Int Int )
    (optokeyedt___arr_element optokeyedt Int datat )
    (optokeyedt___arr_update optokeyedt Int datat optokeyedt )
    (optokeyedt___bit_eq optokeyedt optokeyedt Int )
    (optokeyedt___mk_const_arr datat optokeyedt )
    (prf_rolepresent t Int )
    (privtoavailopst___arr_element
      privtoavailopst
      Int
      availopst
    )
    (privtoavailopst___arr_update
      privtoavailopst
      Int
      availopst
      privtoavailopst
    )
    (privtoavailopst___bit_eq
      privtoavailopst
      privtoavailopst
      Int
    )
    (privtoavailopst___mk_const_arr availopst privtoavailopst )
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
    (string___arr_element string Int Int )
    (string___arr_update string Int Int string )
    (string___bit_eq string string Int )
    (string___mk_const_arr Int string )
    (t___bit_eq t t Int )
    (t___currentop___rcd_element t Int )
    (t___currentop___rcd_update t Int t )
    (t___rolepresent___rcd_element t Int )
    (t___rolepresent___rcd_update t Int t )
  )
  :extrapreds 
  ( (matched)
    (matched___init)
    (matched___loopinit)
    (availopst___member availopst )
    (bit___type___member Int )
    (int___odd Int )
    (ispresent t )
    (opandnullt__LE Int Int )
    (opandnullt__LT Int Int )
    (opandnullt___member Int )
    (optokeyedt___member optokeyedt )
    (privtoavailopst___member privtoavailopst )
    (privtypes__privileget__LE Int Int )
    (privtypes__privileget__LT Int Int )
    (privtypes__privileget___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
    (t___member t )
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
      (opandnullt___member ?i )
      (= (opandnullt__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (opandnullt___member ?i )
      (= (opandnullt__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (opandnullt___member ?i )
      (implies (< ?i 4 ) (= (opandnullt__succ ?i ) (+ ?i 1 ) ) )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (opandnullt___member ?i )
      (implies (< 0 ?i ) (= (opandnullt__pred ?i ) (- ?i 1 ) ) )
    )
  )
  :assumption
  (= nullop 0 )
  :assumption
  (= archivelog 1 )
  :assumption
  (= updateconfigdata 2 )
  :assumption
  (= overridelock 3 )
  :assumption
  (= shutdownop 4 )
  :assumption
  (=
    isavailable
    (privtoavailopst___arr_update
      (privtoavailopst___arr_update
        (privtoavailopst___arr_update
          privtoavailopst___default_arr
          privtypes__guard
          (availopst___arr_update
            (availopst___mk_const_arr bit___false )
            overridelock
            bit___true
          )
        )
        privtypes__auditmanager
        (availopst___arr_update
          (availopst___mk_const_arr bit___false )
          archivelog
          bit___true
        )
      )
      privtypes__securityofficer
      (availopst___arr_update
        (availopst___arr_update
          (availopst___mk_const_arr bit___false )
          updateconfigdata
          bit___true
        )
        shutdownop
        bit___true
      )
    )
  )
  :assumption
  (forall
      (?I Int )
    (implies
      (opandnullt___member ?I )
      (implies
        (and (<= archivelog ?I ) (<= ?I shutdownop ) )
        (<=
          datalengtht__first
          (datat___length___rcd_element
            (optokeyedt___arr_element optokeyed ?I )
          )
        )
      )
    )
  )
  :assumption
  (forall
      (?I Int )
    (implies
      (opandnullt___member ?I )
      (implies
        (and (<= archivelog ?I ) (<= ?I shutdownop ) )
        (<=
          (datat___length___rcd_element
            (optokeyedt___arr_element optokeyed ?I )
          )
          datalengtht__last
        )
      )
    )
  )
  :assumption
  (forall
      (?I Int )
    (implies
      (opandnullt___member ?I )
      (implies
        (and (<= archivelog ?I ) (<= ?I shutdownop ) )
        (<=
          datai__first
          (datat___minmatchlength___rcd_element
            (optokeyedt___arr_element optokeyed ?I )
          )
        )
      )
    )
  )
  :assumption
  (forall
      (?I Int )
    (implies
      (opandnullt___member ?I )
      (implies
        (and (<= archivelog ?I ) (<= ?I shutdownop ) )
        (<=
          (datat___minmatchlength___rcd_element
            (optokeyedt___arr_element optokeyed ?I )
          )
          datai__last
        )
      )
    )
  )
  :assumption
  (forall
      (?I Int ) (?J Int )
    (implies
      (opandnullt___member ?I )
      (implies
        (and
          (<= archivelog ?I )
          (<= ?I shutdownop )
          (<= 1 ?J )
          (<= ?J 18 )
        )
        (<=
          character__first
          (string___arr_element
            (datat___text___rcd_element
              (optokeyedt___arr_element optokeyed ?I )
            )
            ?J
          )
        )
      )
    )
  )
  :assumption
  (forall
      (?I Int ) (?J Int )
    (implies
      (opandnullt___member ?I )
      (implies
        (and
          (<= archivelog ?I )
          (<= ?I shutdownop )
          (<= 1 ?J )
          (<= ?J 18 )
        )
        (<=
          (string___arr_element
            (datat___text___rcd_element
              (optokeyedt___arr_element optokeyed ?I )
            )
            ?J
          )
          character__last
        )
      )
    )
  )
  :assumption
  (=
    optokeyed
    (optokeyedt___arr_update
      (optokeyedt___arr_update
        (optokeyedt___arr_update
          (optokeyedt___arr_update
            optokeyedt___default_arr
            archivelog
            (datat___text___rcd_update
              (datat___minmatchlength___rcd_update
                (datat___length___rcd_update datat___default_rcd 11 )
                7
              )
              (string___arr_update
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update string___default_arr 1 65 )
                                                2
                                                82
                                              )
                                              3
                                              67
                                            )
                                            4
                                            72
                                          )
                                          5
                                          73
                                        )
                                        6
                                        86
                                      )
                                      7
                                      69
                                    )
                                    8
                                    32
                                  )
                                  9
                                  76
                                )
                                10
                                79
                              )
                              11
                              71
                            )
                            12
                            32
                          )
                          13
                          32
                        )
                        14
                        32
                      )
                      15
                      32
                    )
                    16
                    32
                  )
                  17
                  32
                )
                18
                32
              )
            )
          )
          updateconfigdata
          (datat___text___rcd_update
            (datat___minmatchlength___rcd_update
              (datat___length___rcd_update datat___default_rcd 18 )
              6
            )
            (string___arr_update
              (string___arr_update
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update string___default_arr 1 85 )
                                              2
                                              80
                                            )
                                            3
                                            68
                                          )
                                          4
                                          65
                                        )
                                        5
                                        84
                                      )
                                      6
                                      69
                                    )
                                    7
                                    32
                                  )
                                  8
                                  67
                                )
                                9
                                79
                              )
                              10
                              78
                            )
                            11
                            70
                          )
                          12
                          73
                        )
                        13
                        71
                      )
                      14
                      32
                    )
                    15
                    68
                  )
                  16
                  65
                )
                17
                84
              )
              18
              65
            )
          )
        )
        overridelock
        (datat___text___rcd_update
          (datat___minmatchlength___rcd_update
            (datat___length___rcd_update datat___default_rcd 13 )
            8
          )
          (string___arr_update
            (string___arr_update
              (string___arr_update
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update string___default_arr 1 79 )
                                            2
                                            86
                                          )
                                          3
                                          69
                                        )
                                        4
                                        82
                                      )
                                      5
                                      82
                                    )
                                    6
                                    73
                                  )
                                  7
                                  68
                                )
                                8
                                69
                              )
                              9
                              32
                            )
                            10
                            76
                          )
                          11
                          79
                        )
                        12
                        67
                      )
                      13
                      75
                    )
                    14
                    32
                  )
                  15
                  32
                )
                16
                32
              )
              17
              32
            )
            18
            32
          )
        )
      )
      shutdownop
      (datat___text___rcd_update
        (datat___minmatchlength___rcd_update
          (datat___length___rcd_update datat___default_rcd 8 )
          8
        )
        (string___arr_update
          (string___arr_update
            (string___arr_update
              (string___arr_update
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update string___default_arr 1 83 )
                                          2
                                          72
                                        )
                                        3
                                        85
                                      )
                                      4
                                      84
                                    )
                                    5
                                    68
                                  )
                                  6
                                  79
                                )
                                7
                                87
                              )
                              8
                              78
                            )
                            9
                            32
                          )
                          10
                          32
                        )
                        11
                        32
                      )
                      12
                      32
                    )
                    13
                    32
                  )
                  14
                  32
                )
                15
                32
              )
              16
              32
            )
            17
            32
          )
          18
          32
        )
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
  (<= 0 character__size )
  :assumption
  (= character__first 0 )
  :assumption
  (= character__last 255 )
  :assumption
  (= character__base__first 0 )
  :assumption
  (= character__base__last 255 )
  :assumption
  (<= 0 positive__size )
  :assumption
  (= positive__first 1 )
  :assumption
  (= positive__last 2147483647 )
  :assumption
  (= positive__base__first (~ 2147483648 ) )
  :assumption
  (= positive__base__last 2147483647 )
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
  (<= 0 privtypes__adminprivileget__size )
  :assumption
  (= privtypes__adminprivileget__first privtypes__guard )
  :assumption
  (=
    privtypes__adminprivileget__last
    privtypes__securityofficer
  )
  :assumption
  (=
    privtypes__adminprivileget__base__first
    privtypes__useronly
  )
  :assumption
  (=
    privtypes__adminprivileget__base__last
    privtypes__securityofficer
  )
  :assumption
  (<= 0 keyboard__datalengtht__size )
  :assumption
  (= keyboard__datalengtht__first 0 )
  :assumption
  (= keyboard__datalengtht__last 78 )
  :assumption
  (= keyboard__datalengtht__base__first (~ 2147483648 ) )
  :assumption
  (= keyboard__datalengtht__base__last 2147483647 )
  :assumption
  (<= 0 keyboard__datai__size )
  :assumption
  (= keyboard__datai__first 1 )
  :assumption
  (= keyboard__datai__last 78 )
  :assumption
  (= keyboard__datai__base__first (~ 2147483648 ) )
  :assumption
  (= keyboard__datai__base__last 2147483647 )
  :assumption
  (<= 0 opandnullt__size )
  :assumption
  (= opandnullt__first nullop )
  :assumption
  (= opandnullt__last shutdownop )
  :assumption
  (= opandnullt__base__first nullop )
  :assumption
  (= opandnullt__base__last shutdownop )
  :assumption
  (<= 0 opt__size )
  :assumption
  (= opt__first archivelog )
  :assumption
  (= opt__last shutdownop )
  :assumption
  (= opt__base__first nullop )
  :assumption
  (= opt__base__last shutdownop )
  :assumption
  (<= 0 datalengtht__size )
  :assumption
  (= datalengtht__first 0 )
  :assumption
  (= datalengtht__last 18 )
  :assumption
  (= datalengtht__base__first (~ 2147483648 ) )
  :assumption
  (= datalengtht__base__last 2147483647 )
  :assumption
  (<= 0 datai__size )
  :assumption
  (= datai__first 1 )
  :assumption
  (= datai__last 18 )
  :assumption
  (= datai__base__first (~ 2147483648 ) )
  :assumption
  (= datai__base__last 2147483647 )
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
  (opandnullt___member archivelog )
  :assumption
  (privtoavailopst___member isavailable )
  :assumption
  (opandnullt___member loop__1__op )
  :assumption
  (opandnullt___member loop__1__op___init )
  :assumption
  (opandnullt___member loop__1__op___loopinit )
  :assumption
  (opandnullt___member nullop )
  :assumption
  (opandnullt___member opandnullt__base__first )
  :assumption
  (opandnullt___member opandnullt__base__last )
  :assumption
  (opandnullt___member opandnullt__first )
  :assumption
  (opandnullt___member opandnullt__last )
  :assumption
  (opandnullt___member opt__base__first )
  :assumption
  (opandnullt___member opt__base__last )
  :assumption
  (opandnullt___member opt__first )
  :assumption
  (opandnullt___member opt__last )
  :assumption
  (optokeyedt___member optokeyed )
  :assumption
  (opandnullt___member overridelock )
  :assumption
  (privtypes__privileget___member
    privtypes__adminprivileget__base__first
  )
  :assumption
  (privtypes__privileget___member
    privtypes__adminprivileget__base__last
  )
  :assumption
  (privtypes__privileget___member
    privtypes__adminprivileget__first
  )
  :assumption
  (privtypes__privileget___member
    privtypes__adminprivileget__last
  )
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
  (opandnullt___member shutdownop )
  :assumption
  (t___member theadmin )
  :assumption
  (t___member theadmin___init )
  :assumption
  (t___member theadmin___loopinit )
  :assumption
  (opandnullt___member theop )
  :assumption
  (opandnullt___member theop___init )
  :assumption
  (opandnullt___member theop___loopinit )
  :assumption
  (opandnullt___member updateconfigdata )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (opandnullt___member ?x0 )
      (opandnullt___member (opandnullt__pred ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (opandnullt___member ?x0 )
      (opandnullt___member (opandnullt__succ ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (opandnullt___member (opandnullt__val ?x0 ) )
  )
  :assumption
  (forall
      (?x0 t )
    (implies
      (t___member ?x0 )
      (privtypes__privileget___member (prf_rolepresent ?x0 ) )
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
      (?x availopst )
    (iff
      (availopst___member ?x )
      (forall
          (?s0 Int )
        (and
          (implies
            (opandnullt___member ?s0 )
            (bit___type___member (availopst___arr_element ?x ?s0 ) )
          )
          (implies
            (not (opandnullt___member ?s0 ) )
            (=
              (availopst___arr_element ?x ?s0 )
              availopst___default_arr_element
            )
          )
        )
      )
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
      (opandnullt___member ?x )
      (and (<= 0 ?x ) (<= ?x 4 ) )
    )
  )
  :assumption
  (forall
      (?x optokeyedt )
    (iff
      (optokeyedt___member ?x )
      (forall
          (?s0 Int )
        (and
          (implies (opandnullt___member ?s0 ) true )
          (implies
            (not (opandnullt___member ?s0 ) )
            (=
              (optokeyedt___arr_element ?x ?s0 )
              optokeyedt___default_arr_element
            )
          )
        )
      )
    )
  )
  :assumption
  (forall
      (?x privtoavailopst )
    (iff
      (privtoavailopst___member ?x )
      (forall
          (?s0 Int )
        (and
          (implies
            (privtypes__privileget___member ?s0 )
            (availopst___member
              (privtoavailopst___arr_element ?x ?s0 )
            )
          )
          (implies
            (not (privtypes__privileget___member ?s0 ) )
            (=
              (privtoavailopst___arr_element ?x ?s0 )
              privtoavailopst___default_arr_element
            )
          )
        )
      )
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
      (?x t )
    (iff
      (t___member ?x )
      (and
        (privtypes__privileget___member
          (t___rolepresent___rcd_element ?x )
        )
        (opandnullt___member (t___currentop___rcd_element ?x ) )
      )
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
      (?x availopst ) (?y availopst )
    (iff
      (= (availopst___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (character___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x datat ) (?y datat )
    (iff (= (datat___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x keyboard__datat ) (?y keyboard__datat )
    (iff
      (= (keyboard__datat___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (opandnullt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x optokeyedt ) (?y optokeyedt )
    (iff
      (= (optokeyedt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x privtoavailopst ) (?y privtoavailopst )
    (iff
      (= (privtoavailopst___bit_eq ?x ?y ) bit___true )
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
      (?x string ) (?y string )
    (iff (= (string___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x t ) (?y t )
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
      (?i1 Int ) (?v Int )
    (=
      (string___arr_element (string___mk_const_arr ?v ) ?i1 )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v Int )
    (=
      (availopst___arr_element
        (availopst___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v availopst )
    (=
      (privtoavailopst___arr_element
        (privtoavailopst___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v datat )
    (=
      (optokeyedt___arr_element
        (optokeyedt___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a availopst ) (?s0 Int ) (?t Int )
    (=
      (availopst___arr_element
        (availopst___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a availopst ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (availopst___arr_element
          (availopst___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (availopst___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a optokeyedt ) (?s0 Int ) (?t datat )
    (=
      (optokeyedt___arr_element
        (optokeyedt___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a optokeyedt ) (?s0 Int ) (?s0p Int ) (?t datat )
    (or
      (= ?s0 ?s0p )
      (=
        (optokeyedt___arr_element
          (optokeyedt___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (optokeyedt___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a privtoavailopst ) (?s0 Int ) (?t availopst )
    (=
      (privtoavailopst___arr_element
        (privtoavailopst___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a privtoavailopst )
      (?s0 Int )
      (?s0p Int )
      (?t availopst )
    (or
      (= ?s0 ?s0p )
      (=
        (privtoavailopst___arr_element
          (privtoavailopst___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (privtoavailopst___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a string ) (?s0 Int ) (?t Int )
    (=
      (string___arr_element (string___arr_update ?a ?s0 ?t ) ?s0 )
      ?t
    )
  )
  :assumption
  (forall
      (?a string ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (string___arr_element
          (string___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (string___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?r t ) (?t Int )
    (=
      (t___rolepresent___rcd_element
        (t___rolepresent___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r t ) (?t Int )
    (=
      (t___rolepresent___rcd_element
        (t___currentop___rcd_update ?r ?t )
      )
      (t___rolepresent___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r t ) (?t Int )
    (=
      (t___currentop___rcd_element
        (t___rolepresent___rcd_update ?r ?t )
      )
      (t___currentop___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r t ) (?t Int )
    (=
      (t___currentop___rcd_element
        (t___currentop___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r keyboard__datat ) (?t Int )
    (=
      (keyboard__datat___length___rcd_element
        (keyboard__datat___length___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r keyboard__datat ) (?t string )
    (=
      (keyboard__datat___length___rcd_element
        (keyboard__datat___text___rcd_update ?r ?t )
      )
      (keyboard__datat___length___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keyboard__datat ) (?t Int )
    (=
      (keyboard__datat___text___rcd_element
        (keyboard__datat___length___rcd_update ?r ?t )
      )
      (keyboard__datat___text___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keyboard__datat ) (?t string )
    (=
      (keyboard__datat___text___rcd_element
        (keyboard__datat___text___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r datat ) (?t Int )
    (=
      (datat___length___rcd_element
        (datat___length___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r datat ) (?t Int )
    (=
      (datat___length___rcd_element
        (datat___minmatchlength___rcd_update ?r ?t )
      )
      (datat___length___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r datat ) (?t string )
    (=
      (datat___length___rcd_element
        (datat___text___rcd_update ?r ?t )
      )
      (datat___length___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r datat ) (?t Int )
    (=
      (datat___minmatchlength___rcd_element
        (datat___length___rcd_update ?r ?t )
      )
      (datat___minmatchlength___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r datat ) (?t Int )
    (=
      (datat___minmatchlength___rcd_element
        (datat___minmatchlength___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r datat ) (?t string )
    (=
      (datat___minmatchlength___rcd_element
        (datat___text___rcd_update ?r ?t )
      )
      (datat___minmatchlength___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r datat ) (?t Int )
    (=
      (datat___text___rcd_element
        (datat___length___rcd_update ?r ?t )
      )
      (datat___text___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r datat ) (?t Int )
    (=
      (datat___text___rcd_element
        (datat___minmatchlength___rcd_update ?r ?t )
      )
      (datat___text___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r datat ) (?t string )
    (=
      (datat___text___rcd_element
        (datat___text___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (<= nullop (t___currentop___rcd_element theadmin ) )
    (<= (t___currentop___rcd_element theadmin ) shutdownop )
    (<=
      privtypes__useronly
      (t___rolepresent___rcd_element theadmin )
    )
    (<=
      (t___rolepresent___rcd_element theadmin )
      privtypes__securityofficer
    )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 78 ) )
        (and
          (<=
            0
            (string___arr_element
              (keyboard__datat___text___rcd_element keyedop )
              ?i___1
            )
          )
          (<=
            (string___arr_element
              (keyboard__datat___text___rcd_element keyedop )
              ?i___1
            )
            255
          )
        )
      )
    )
    (<= 0 (keyboard__datat___length___rcd_element keyedop ) )
    (<= (keyboard__datat___length___rcd_element keyedop ) 78 )
    (ispresent theadmin )
    (<= archivelog loop__1__op )
    (<= loop__1__op shutdownop )
    (<=
      (datat___minmatchlength___rcd_element
        (optokeyedt___arr_element
          (optokeyedt___arr_update
            (optokeyedt___arr_update
              (optokeyedt___arr_update
                (optokeyedt___arr_update
                  optokeyedt___default_arr
                  archivelog
                  (datat___text___rcd_update
                    (datat___minmatchlength___rcd_update
                      (datat___length___rcd_update datat___default_rcd 11 )
                      7
                    )
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update
                                                  (string___arr_update
                                                    (string___arr_update
                                                      (string___arr_update string___default_arr 1 65 )
                                                      2
                                                      82
                                                    )
                                                    3
                                                    67
                                                  )
                                                  4
                                                  72
                                                )
                                                5
                                                73
                                              )
                                              6
                                              86
                                            )
                                            7
                                            69
                                          )
                                          8
                                          32
                                        )
                                        9
                                        76
                                      )
                                      10
                                      79
                                    )
                                    11
                                    71
                                  )
                                  12
                                  32
                                )
                                13
                                32
                              )
                              14
                              32
                            )
                            15
                            32
                          )
                          16
                          32
                        )
                        17
                        32
                      )
                      18
                      32
                    )
                  )
                )
                updateconfigdata
                (datat___text___rcd_update
                  (datat___minmatchlength___rcd_update
                    (datat___length___rcd_update datat___default_rcd 18 )
                    6
                  )
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update
                                                  (string___arr_update
                                                    (string___arr_update string___default_arr 1 85 )
                                                    2
                                                    80
                                                  )
                                                  3
                                                  68
                                                )
                                                4
                                                65
                                              )
                                              5
                                              84
                                            )
                                            6
                                            69
                                          )
                                          7
                                          32
                                        )
                                        8
                                        67
                                      )
                                      9
                                      79
                                    )
                                    10
                                    78
                                  )
                                  11
                                  70
                                )
                                12
                                73
                              )
                              13
                              71
                            )
                            14
                            32
                          )
                          15
                          68
                        )
                        16
                        65
                      )
                      17
                      84
                    )
                    18
                    65
                  )
                )
              )
              overridelock
              (datat___text___rcd_update
                (datat___minmatchlength___rcd_update
                  (datat___length___rcd_update datat___default_rcd 13 )
                  8
                )
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update
                                                  (string___arr_update string___default_arr 1 79 )
                                                  2
                                                  86
                                                )
                                                3
                                                69
                                              )
                                              4
                                              82
                                            )
                                            5
                                            82
                                          )
                                          6
                                          73
                                        )
                                        7
                                        68
                                      )
                                      8
                                      69
                                    )
                                    9
                                    32
                                  )
                                  10
                                  76
                                )
                                11
                                79
                              )
                              12
                              67
                            )
                            13
                            75
                          )
                          14
                          32
                        )
                        15
                        32
                      )
                      16
                      32
                    )
                    17
                    32
                  )
                  18
                  32
                )
              )
            )
            shutdownop
            (datat___text___rcd_update
              (datat___minmatchlength___rcd_update
                (datat___length___rcd_update datat___default_rcd 8 )
                8
              )
              (string___arr_update
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update string___default_arr 1 83 )
                                                2
                                                72
                                              )
                                              3
                                              85
                                            )
                                            4
                                            84
                                          )
                                          5
                                          68
                                        )
                                        6
                                        79
                                      )
                                      7
                                      87
                                    )
                                    8
                                    78
                                  )
                                  9
                                  32
                                )
                                10
                                32
                              )
                              11
                              32
                            )
                            12
                            32
                          )
                          13
                          32
                        )
                        14
                        32
                      )
                      15
                      32
                    )
                    16
                    32
                  )
                  17
                  32
                )
                18
                32
              )
            )
          )
          loop__1__op
        )
      )
      (keyboard__datat___length___rcd_element keyedop )
    )
    (<=
      (keyboard__datat___length___rcd_element keyedop )
      (datat___length___rcd_element
        (optokeyedt___arr_element
          (optokeyedt___arr_update
            (optokeyedt___arr_update
              (optokeyedt___arr_update
                (optokeyedt___arr_update
                  optokeyedt___default_arr
                  archivelog
                  (datat___text___rcd_update
                    (datat___minmatchlength___rcd_update
                      (datat___length___rcd_update datat___default_rcd 11 )
                      7
                    )
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update
                                                  (string___arr_update
                                                    (string___arr_update
                                                      (string___arr_update string___default_arr 1 65 )
                                                      2
                                                      82
                                                    )
                                                    3
                                                    67
                                                  )
                                                  4
                                                  72
                                                )
                                                5
                                                73
                                              )
                                              6
                                              86
                                            )
                                            7
                                            69
                                          )
                                          8
                                          32
                                        )
                                        9
                                        76
                                      )
                                      10
                                      79
                                    )
                                    11
                                    71
                                  )
                                  12
                                  32
                                )
                                13
                                32
                              )
                              14
                              32
                            )
                            15
                            32
                          )
                          16
                          32
                        )
                        17
                        32
                      )
                      18
                      32
                    )
                  )
                )
                updateconfigdata
                (datat___text___rcd_update
                  (datat___minmatchlength___rcd_update
                    (datat___length___rcd_update datat___default_rcd 18 )
                    6
                  )
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update
                                                  (string___arr_update
                                                    (string___arr_update string___default_arr 1 85 )
                                                    2
                                                    80
                                                  )
                                                  3
                                                  68
                                                )
                                                4
                                                65
                                              )
                                              5
                                              84
                                            )
                                            6
                                            69
                                          )
                                          7
                                          32
                                        )
                                        8
                                        67
                                      )
                                      9
                                      79
                                    )
                                    10
                                    78
                                  )
                                  11
                                  70
                                )
                                12
                                73
                              )
                              13
                              71
                            )
                            14
                            32
                          )
                          15
                          68
                        )
                        16
                        65
                      )
                      17
                      84
                    )
                    18
                    65
                  )
                )
              )
              overridelock
              (datat___text___rcd_update
                (datat___minmatchlength___rcd_update
                  (datat___length___rcd_update datat___default_rcd 13 )
                  8
                )
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update
                                                  (string___arr_update string___default_arr 1 79 )
                                                  2
                                                  86
                                                )
                                                3
                                                69
                                              )
                                              4
                                              82
                                            )
                                            5
                                            82
                                          )
                                          6
                                          73
                                        )
                                        7
                                        68
                                      )
                                      8
                                      69
                                    )
                                    9
                                    32
                                  )
                                  10
                                  76
                                )
                                11
                                79
                              )
                              12
                              67
                            )
                            13
                            75
                          )
                          14
                          32
                        )
                        15
                        32
                      )
                      16
                      32
                    )
                    17
                    32
                  )
                  18
                  32
                )
              )
            )
            shutdownop
            (datat___text___rcd_update
              (datat___minmatchlength___rcd_update
                (datat___length___rcd_update datat___default_rcd 8 )
                8
              )
              (string___arr_update
                (string___arr_update
                  (string___arr_update
                    (string___arr_update
                      (string___arr_update
                        (string___arr_update
                          (string___arr_update
                            (string___arr_update
                              (string___arr_update
                                (string___arr_update
                                  (string___arr_update
                                    (string___arr_update
                                      (string___arr_update
                                        (string___arr_update
                                          (string___arr_update
                                            (string___arr_update
                                              (string___arr_update
                                                (string___arr_update string___default_arr 1 83 )
                                                2
                                                72
                                              )
                                              3
                                              85
                                            )
                                            4
                                            84
                                          )
                                          5
                                          68
                                        )
                                        6
                                        79
                                      )
                                      7
                                      87
                                    )
                                    8
                                    78
                                  )
                                  9
                                  32
                                )
                                10
                                32
                              )
                              11
                              32
                            )
                            12
                            32
                          )
                          13
                          32
                        )
                        14
                        32
                      )
                      15
                      32
                    )
                    16
                    32
                  )
                  17
                  32
                )
                18
                32
              )
            )
          )
          loop__1__op
        )
      )
    )
    (<= 0 integer__size )
    (<= 0 character__size )
    (<= 0 positive__size )
    (<= 0 privtypes__privileget__size )
    (<= 0 privtypes__adminprivileget__size )
    (<= 0 keyboard__datalengtht__size )
    (<= 0 keyboard__datai__size )
    (<= 0 opandnullt__size )
    (<= 0 opt__size )
    (<= 0 datalengtht__size )
    (<= 0 datai__size )
    (not
      (and
        (<= 1 (keyboard__datat___length___rcd_element keyedop ) )
        (<= (keyboard__datat___length___rcd_element keyedop ) 18 )
      )
    )
  )
  :status unknown
)
