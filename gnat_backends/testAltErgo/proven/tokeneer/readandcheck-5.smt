(benchmark readandcheck.5.1
  :logic AUFNIRA
  :extrasorts 
  ( cert__contentst
    admintoken__interface__state__type
    admintoken__interface__status__type
    admintoken__interface__input__type
    string
    cert__attr__contentst
    cert__id__contentst
    status__type
    input__type
    cert__attr__auth__contentst
    valididcertt
    validauthcertt
    statetype
    real___type
  )
  :extrafuns 
  ( (admintoken__interface__input
      admintoken__interface__input__type
    )
    (admintoken__interface__input___init
      admintoken__interface__input__type
    )
    (admintoken__interface__input___loopinit
      admintoken__interface__input__type
    )
    (admintoken__interface__state
      admintoken__interface__state__type
    )
    (admintoken__interface__state___init
      admintoken__interface__state__type
    )
    (admintoken__interface__state___loopinit
      admintoken__interface__state__type
    )
    (admintoken__interface__status
      admintoken__interface__status__type
    )
    (admintoken__interface__status___init
      admintoken__interface__status__type
    )
    (admintoken__interface__status___loopinit
      admintoken__interface__status__type
    )
    (audittypes__descriptioni__base__first Int )
    (audittypes__descriptioni__base__last Int )
    (audittypes__descriptioni__first Int )
    (audittypes__descriptioni__last Int )
    (audittypes__descriptioni__size Int )
    (authcert validauthcertt )
    (authcert___init validauthcertt )
    (authcert___loopinit validauthcertt )
    (authcertcontents cert__attr__auth__contentst )
    (authcertcontents__1 cert__attr__auth__contentst )
    (authcertcontents__1___init cert__attr__auth__contentst )
    (authcertcontents__1___loopinit
      cert__attr__auth__contentst
    )
    (authcertcontents__4 cert__attr__auth__contentst )
    (authcertcontents__4___init cert__attr__auth__contentst )
    (authcertcontents__4___loopinit
      cert__attr__auth__contentst
    )
    (authcertcontents___init cert__attr__auth__contentst )
    (authcertcontents___loopinit cert__attr__auth__contentst )
    (basictypes__absent Int )
    (basictypes__presencet__base__first Int )
    (basictypes__presencet__base__last Int )
    (basictypes__presencet__first Int )
    (basictypes__presencet__last Int )
    (basictypes__presencet__size Int )
    (basictypes__present Int )
    (basictypes__unsigned32t__base__first Int )
    (basictypes__unsigned32t__base__last Int )
    (basictypes__unsigned32t__first Int )
    (basictypes__unsigned32t__last Int )
    (basictypes__unsigned32t__size Int )
    (bit___false Int )
    (bit___true Int )
    (cert__attr__auth__contentst___default_rcd
      cert__attr__auth__contentst
    )
    (cert__attr__auth__contentst__size Int )
    (cert__attr__contentst___default_rcd cert__attr__contentst )
    (cert__attr__contentst__size Int )
    (cert__id__contentst___default_rcd cert__id__contentst )
    (cert__id__contentst__size Int )
    (character__base__first Int )
    (character__base__last Int )
    (character__first Int )
    (character__last Int )
    (character__size Int )
    (description string )
    (description__3 string )
    (description__3___init string )
    (description__3___loopinit string )
    (description__4 string )
    (description__4___init string )
    (description__4___loopinit string )
    (description___init string )
    (description___loopinit string )
    (idcert valididcertt )
    (idcert___init valididcertt )
    (idcert___loopinit valididcertt )
    (idcertcontents cert__id__contentst )
    (idcertcontents__2 cert__id__contentst )
    (idcertcontents__2___init cert__id__contentst )
    (idcertcontents__2___loopinit cert__id__contentst )
    (idcertcontents__3 cert__id__contentst )
    (idcertcontents__3___init cert__id__contentst )
    (idcertcontents__3___loopinit cert__id__contentst )
    (idcertcontents___init cert__id__contentst )
    (idcertcontents___loopinit cert__id__contentst )
    (input input__type )
    (input___init input__type )
    (input___loopinit input__type )
    (input__type___default_rcd input__type )
    (input__type__size Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (null__string string )
    (positive__base__first Int )
    (positive__base__last Int )
    (positive__first Int )
    (positive__last Int )
    (positive__size Int )
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
    (state statetype )
    (state___init statetype )
    (state___loopinit statetype )
    (statetype___default_rcd statetype )
    (statetype__size Int )
    (status' status__type )
    (status___init status__type )
    (status___loopinit status__type )
    (status__type___default_rcd status__type )
    (status__type__size Int )
    (string___default_arr string )
    (string___default_arr_element Int )
    (tokenid Int )
    (tokenid___init Int )
    (tokenid___loopinit Int )
    (tokenpresence Int )
    (tokenpresence___init Int )
    (tokenpresence___loopinit Int )
    (tokentry Int )
    (tokentry___init Int )
    (tokentry___loopinit Int )
    (tokentypes__badtoken Int )
    (tokentypes__goodtoken Int )
    (tokentypes__notoken Int )
    (tokentypes__tokenidt__base__first Int )
    (tokentypes__tokenidt__base__last Int )
    (tokentypes__tokenidt__first Int )
    (tokentypes__tokenidt__last Int )
    (tokentypes__tokenidt__size Int )
    (tokentypes__tryt__base__first Int )
    (tokentypes__tryt__base__last Int )
    (tokentypes__tryt__first Int )
    (tokentypes__tryt__last Int )
    (tokentypes__tryt__size Int )
    (validauthcertt___default_rcd validauthcertt )
    (validauthcertt__size Int )
    (valididcertt___default_rcd valididcertt )
    (valididcertt__size Int )
    (admintoken__interface__input__type___bit_eq
      admintoken__interface__input__type
      admintoken__interface__input__type
      Int
    )
    (admintoken__interface__state__type___bit_eq
      admintoken__interface__state__type
      admintoken__interface__state__type
      Int
    )
    (admintoken__interface__status__type___bit_eq
      admintoken__interface__status__type
      admintoken__interface__status__type
      Int
    )
    (admintoken__interface__thetokenid
      admintoken__interface__state__type
      Int
    )
    (admintoken__interface__thetokentry
      admintoken__interface__state__type
      Int
    )
    (basictypes__presencet___bit_eq Int Int Int )
    (basictypes__presencet__pos Int Int )
    (basictypes__presencet__pred Int Int )
    (basictypes__presencet__succ Int Int )
    (basictypes__presencet__val Int Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (bit__and Int Int Int )
    (bit__not Int Int Int )
    (bit__or Int Int Int )
    (bit__xor Int Int Int )
    (cert__attr__auth__contentst___bit_eq
      cert__attr__auth__contentst
      cert__attr__auth__contentst
      Int
    )
    (cert__attr__auth__contentst___inherit___rcd_element
      cert__attr__auth__contentst
      cert__attr__contentst
    )
    (cert__attr__auth__contentst___inherit___rcd_update
      cert__attr__auth__contentst
      cert__attr__contentst
      cert__attr__auth__contentst
    )
    (cert__attr__auth__therole cert__attr__auth__contentst Int )
    (cert__attr__contentst___bit_eq
      cert__attr__contentst
      cert__attr__contentst
      Int
    )
    (cert__attr__contentst___inherit___rcd_element
      cert__attr__contentst
      cert__contentst
    )
    (cert__attr__contentst___inherit___rcd_update
      cert__attr__contentst
      cert__contentst
      cert__attr__contentst
    )
    (cert__contentst___bit_eq
      cert__contentst
      cert__contentst
      Int
    )
    (cert__id__contentst___bit_eq
      cert__id__contentst
      cert__id__contentst
      Int
    )
    (cert__id__contentst___inherit___rcd_element
      cert__id__contentst
      cert__contentst
    )
    (cert__id__contentst___inherit___rcd_update
      cert__id__contentst
      cert__contentst
      cert__id__contentst
    )
    (character___bit_eq Int Int Int )
    (character__pos Int Int )
    (character__val Int Int )
    (input__type___admintoken__interface__input___rcd_element
      input__type
      admintoken__interface__input__type
    )
    (input__type___admintoken__interface__input___rcd_update
      input__type
      admintoken__interface__input__type
      input__type
    )
    (input__type___bit_eq input__type input__type Int )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (makedescription string string )
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
    (statetype___admintoken__interface__state___rcd_element
      statetype
      admintoken__interface__state__type
    )
    (statetype___admintoken__interface__state___rcd_update
      statetype
      admintoken__interface__state__type
      statetype
    )
    (statetype___authcert___rcd_element
      statetype
      validauthcertt
    )
    (statetype___authcert___rcd_update
      statetype
      validauthcertt
      statetype
    )
    (statetype___bit_eq statetype statetype Int )
    (statetype___idcert___rcd_element statetype valididcertt )
    (statetype___idcert___rcd_update
      statetype
      valididcertt
      statetype
    )
    (statetype___tokenid___rcd_element statetype Int )
    (statetype___tokenid___rcd_update statetype Int statetype )
    (statetype___tokenpresence___rcd_element statetype Int )
    (statetype___tokenpresence___rcd_update
      statetype
      Int
      statetype
    )
    (statetype___tokentry___rcd_element statetype Int )
    (statetype___tokentry___rcd_update statetype Int statetype )
    (status__type___admintoken__interface__status___rcd_element
      status__type
      admintoken__interface__status__type
    )
    (status__type___admintoken__interface__status___rcd_update
      status__type
      admintoken__interface__status__type
      status__type
    )
    (status__type___bit_eq status__type status__type Int )
    (string___arr_element string Int Int )
    (string___arr_update string Int Int string )
    (string___bit_eq string string Int )
    (string___mk_const_arr Int string )
    (theauthcertrole statetype Int )
    (tokentypes__tryt___bit_eq Int Int Int )
    (tokentypes__tryt__pos Int Int )
    (tokentypes__tryt__pred Int Int )
    (tokentypes__tryt__succ Int Int )
    (tokentypes__tryt__val Int Int )
    (validauthcertt___bit_eq validauthcertt validauthcertt Int )
    (validauthcertt___contents___rcd_element
      validauthcertt
      cert__attr__auth__contentst
    )
    (validauthcertt___contents___rcd_update
      validauthcertt
      cert__attr__auth__contentst
      validauthcertt
    )
    (validauthcertt___valid___rcd_element validauthcertt Int )
    (validauthcertt___valid___rcd_update
      validauthcertt
      Int
      validauthcertt
    )
    (valididcertt___bit_eq valididcertt valididcertt Int )
    (valididcertt___contents___rcd_element
      valididcertt
      cert__id__contentst
    )
    (valididcertt___contents___rcd_update
      valididcertt
      cert__id__contentst
      valididcertt
    )
    (valididcertt___valid___rcd_element valididcertt Int )
    (valididcertt___valid___rcd_update
      valididcertt
      Int
      valididcertt
    )
  )
  :extrapreds 
  ( (authvalid)
    (authvalid__4)
    (authvalid__4___init)
    (authvalid__4___loopinit)
    (authvalid___init)
    (authvalid___loopinit)
    (idvalid)
    (idvalid__3)
    (idvalid__3___init)
    (idvalid__3___loopinit)
    (idvalid___init)
    (idvalid___loopinit)
    (tokenok)
    (tokenok___init)
    (tokenok___loopinit)
    (basictypes__presencet__LE Int Int )
    (basictypes__presencet__LT Int Int )
    (basictypes__presencet___member Int )
    (bit___type___member Int )
    (int___odd Int )
    (prf_authcertvalid statetype )
    (prf_isgood statetype )
    (privtypes__privileget__LE Int Int )
    (privtypes__privileget__LT Int Int )
    (privtypes__privileget___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
    (statetype___member statetype )
    (tokentypes__tryt__LE Int Int )
    (tokentypes__tryt__LT Int Int )
    (tokentypes__tryt___member Int )
    (validauthcertt___member validauthcertt )
    (valididcertt___member valididcertt )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (basictypes__presencet___member ?i )
      (= (basictypes__presencet__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (basictypes__presencet___member ?i )
      (= (basictypes__presencet__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (basictypes__presencet___member ?i )
      (implies
        (< ?i 1 )
        (= (basictypes__presencet__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (basictypes__presencet___member ?i )
      (implies
        (< 0 ?i )
        (= (basictypes__presencet__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= basictypes__present 0 )
  :assumption
  (= basictypes__absent 1 )
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
      (tokentypes__tryt___member ?i )
      (= (tokentypes__tryt__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (tokentypes__tryt___member ?i )
      (= (tokentypes__tryt__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (tokentypes__tryt___member ?i )
      (implies
        (< ?i 2 )
        (= (tokentypes__tryt__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (tokentypes__tryt___member ?i )
      (implies
        (< 0 ?i )
        (= (tokentypes__tryt__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= tokentypes__notoken 0 )
  :assumption
  (= tokentypes__badtoken 1 )
  :assumption
  (= tokentypes__goodtoken 2 )
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
  (<= 0 basictypes__unsigned32t__size )
  :assumption
  (= basictypes__unsigned32t__size 32 )
  :assumption
  (= basictypes__unsigned32t__first 0 )
  :assumption
  (= basictypes__unsigned32t__last 4294967295 )
  :assumption
  (<=
    basictypes__unsigned32t__base__first
    basictypes__unsigned32t__base__last
  )
  :assumption
  (<=
    basictypes__unsigned32t__base__first
    basictypes__unsigned32t__first
  )
  :assumption
  (<=
    basictypes__unsigned32t__last
    basictypes__unsigned32t__base__last
  )
  :assumption
  (<= 0 basictypes__presencet__size )
  :assumption
  (= basictypes__presencet__first basictypes__present )
  :assumption
  (= basictypes__presencet__last basictypes__absent )
  :assumption
  (= basictypes__presencet__base__first basictypes__present )
  :assumption
  (= basictypes__presencet__base__last basictypes__absent )
  :assumption
  (<= 0 audittypes__descriptioni__size )
  :assumption
  (= audittypes__descriptioni__first 1 )
  :assumption
  (= audittypes__descriptioni__last 150 )
  :assumption
  (= audittypes__descriptioni__base__first (~ 2147483648 ) )
  :assumption
  (= audittypes__descriptioni__base__last 2147483647 )
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
  (<= 0 tokentypes__tokenidt__size )
  :assumption
  (= tokentypes__tokenidt__first 0 )
  :assumption
  (= tokentypes__tokenidt__last 4294967295 )
  :assumption
  (<=
    tokentypes__tokenidt__base__first
    tokentypes__tokenidt__base__last
  )
  :assumption
  (<=
    tokentypes__tokenidt__base__first
    tokentypes__tokenidt__first
  )
  :assumption
  (<=
    tokentypes__tokenidt__last
    tokentypes__tokenidt__base__last
  )
  :assumption
  (<= 0 tokentypes__tryt__size )
  :assumption
  (= tokentypes__tryt__first tokentypes__notoken )
  :assumption
  (= tokentypes__tryt__last tokentypes__goodtoken )
  :assumption
  (= tokentypes__tryt__base__first tokentypes__notoken )
  :assumption
  (= tokentypes__tryt__base__last tokentypes__goodtoken )
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
  (validauthcertt___member authcert )
  :assumption
  (validauthcertt___member authcert___init )
  :assumption
  (validauthcertt___member authcert___loopinit )
  :assumption
  (basictypes__presencet___member basictypes__absent )
  :assumption
  (basictypes__presencet___member
    basictypes__presencet__base__first
  )
  :assumption
  (basictypes__presencet___member
    basictypes__presencet__base__last
  )
  :assumption
  (basictypes__presencet___member
    basictypes__presencet__first
  )
  :assumption
  (basictypes__presencet___member
    basictypes__presencet__last
  )
  :assumption
  (basictypes__presencet___member basictypes__present )
  :assumption
  (valididcertt___member idcert )
  :assumption
  (valididcertt___member idcert___init )
  :assumption
  (valididcertt___member idcert___loopinit )
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
  (statetype___member state )
  :assumption
  (statetype___member state___init )
  :assumption
  (statetype___member state___loopinit )
  :assumption
  (basictypes__presencet___member tokenpresence )
  :assumption
  (basictypes__presencet___member tokenpresence___init )
  :assumption
  (basictypes__presencet___member tokenpresence___loopinit )
  :assumption
  (tokentypes__tryt___member tokentry )
  :assumption
  (tokentypes__tryt___member tokentry___init )
  :assumption
  (tokentypes__tryt___member tokentry___loopinit )
  :assumption
  (tokentypes__tryt___member tokentypes__badtoken )
  :assumption
  (tokentypes__tryt___member tokentypes__goodtoken )
  :assumption
  (tokentypes__tryt___member tokentypes__notoken )
  :assumption
  (tokentypes__tryt___member tokentypes__tryt__base__first )
  :assumption
  (tokentypes__tryt___member tokentypes__tryt__base__last )
  :assumption
  (tokentypes__tryt___member tokentypes__tryt__first )
  :assumption
  (tokentypes__tryt___member tokentypes__tryt__last )
  :assumption
  (forall
      (?x0 admintoken__interface__state__type )
    (tokentypes__tryt___member
      (admintoken__interface__thetokentry ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (basictypes__presencet___member ?x0 )
      (basictypes__presencet___member
        (basictypes__presencet__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (basictypes__presencet___member ?x0 )
      (basictypes__presencet___member
        (basictypes__presencet__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (basictypes__presencet___member
      (basictypes__presencet__val ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 cert__attr__auth__contentst )
    (privtypes__privileget___member
      (cert__attr__auth__therole ?x0 )
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
      (?x0 statetype )
    (implies
      (statetype___member ?x0 )
      (privtypes__privileget___member (theauthcertrole ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (tokentypes__tryt___member ?x0 )
      (tokentypes__tryt___member (tokentypes__tryt__pred ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (tokentypes__tryt___member ?x0 )
      (tokentypes__tryt___member (tokentypes__tryt__succ ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (tokentypes__tryt___member (tokentypes__tryt__val ?x0 ) )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (basictypes__presencet___member ?x )
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
      (?x Int )
    (iff
      (privtypes__privileget___member ?x )
      (and (<= 0 ?x ) (<= ?x 3 ) )
    )
  )
  :assumption
  (forall
      (?x statetype )
    (iff
      (statetype___member ?x )
      (and
        true
        (valididcertt___member
          (statetype___idcert___rcd_element ?x )
        )
        (validauthcertt___member
          (statetype___authcert___rcd_element ?x )
        )
        true
        (tokentypes__tryt___member
          (statetype___tokentry___rcd_element ?x )
        )
        (basictypes__presencet___member
          (statetype___tokenpresence___rcd_element ?x )
        )
      )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (tokentypes__tryt___member ?x )
      (and (<= 0 ?x ) (<= ?x 2 ) )
    )
  )
  :assumption
  (forall
      (?x validauthcertt )
    (iff
      (validauthcertt___member ?x )
      (and
        (bit___type___member
          (validauthcertt___valid___rcd_element ?x )
        )
        true
      )
    )
  )
  :assumption
  (forall
      (?x valididcertt )
    (iff
      (valididcertt___member ?x )
      (and
        (bit___type___member
          (valididcertt___valid___rcd_element ?x )
        )
        true
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
      (?x admintoken__interface__input__type )
      (?y admintoken__interface__input__type )
    (iff
      (=
        (admintoken__interface__input__type___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x admintoken__interface__state__type )
      (?y admintoken__interface__state__type )
    (iff
      (=
        (admintoken__interface__state__type___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x admintoken__interface__status__type )
      (?y admintoken__interface__status__type )
    (iff
      (=
        (admintoken__interface__status__type___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (basictypes__presencet___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x cert__attr__auth__contentst )
      (?y cert__attr__auth__contentst )
    (iff
      (=
        (cert__attr__auth__contentst___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x cert__attr__contentst ) (?y cert__attr__contentst )
    (iff
      (= (cert__attr__contentst___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x cert__contentst ) (?y cert__contentst )
    (iff
      (= (cert__contentst___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x cert__id__contentst ) (?y cert__id__contentst )
    (iff
      (= (cert__id__contentst___bit_eq ?x ?y ) bit___true )
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
      (?x input__type ) (?y input__type )
    (iff
      (= (input__type___bit_eq ?x ?y ) bit___true )
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
      (?x statetype ) (?y statetype )
    (iff
      (= (statetype___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x status__type ) (?y status__type )
    (iff
      (= (status__type___bit_eq ?x ?y ) bit___true )
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
      (?x Int ) (?y Int )
    (iff
      (= (tokentypes__tryt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x validauthcertt ) (?y validauthcertt )
    (iff
      (= (validauthcertt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x valididcertt ) (?y valididcertt )
    (iff
      (= (valididcertt___bit_eq ?x ?y ) bit___true )
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
      (string___arr_element (string___mk_const_arr ?v ) ?i1 )
      ?v
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
      (?r cert__attr__contentst ) (?t cert__contentst )
    (=
      (cert__attr__contentst___inherit___rcd_element
        (cert__attr__contentst___inherit___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r cert__id__contentst ) (?t cert__contentst )
    (=
      (cert__id__contentst___inherit___rcd_element
        (cert__id__contentst___inherit___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r status__type )
      (?t admintoken__interface__status__type )
    (=
      (status__type___admintoken__interface__status___rcd_element
        (status__type___admintoken__interface__status___rcd_update
          ?r
          ?t
        )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r input__type ) (?t admintoken__interface__input__type )
    (=
      (input__type___admintoken__interface__input___rcd_element
        (input__type___admintoken__interface__input___rcd_update
          ?r
          ?t
        )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r cert__attr__auth__contentst )
      (?t cert__attr__contentst )
    (=
      (cert__attr__auth__contentst___inherit___rcd_element
        (cert__attr__auth__contentst___inherit___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r valididcertt ) (?t Int )
    (=
      (valididcertt___valid___rcd_element
        (valididcertt___valid___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r valididcertt ) (?t cert__id__contentst )
    (=
      (valididcertt___valid___rcd_element
        (valididcertt___contents___rcd_update ?r ?t )
      )
      (valididcertt___valid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r valididcertt ) (?t Int )
    (=
      (valididcertt___contents___rcd_element
        (valididcertt___valid___rcd_update ?r ?t )
      )
      (valididcertt___contents___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r valididcertt ) (?t cert__id__contentst )
    (=
      (valididcertt___contents___rcd_element
        (valididcertt___contents___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r validauthcertt ) (?t Int )
    (=
      (validauthcertt___valid___rcd_element
        (validauthcertt___valid___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r validauthcertt ) (?t cert__attr__auth__contentst )
    (=
      (validauthcertt___valid___rcd_element
        (validauthcertt___contents___rcd_update ?r ?t )
      )
      (validauthcertt___valid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r validauthcertt ) (?t Int )
    (=
      (validauthcertt___contents___rcd_element
        (validauthcertt___valid___rcd_update ?r ?t )
      )
      (validauthcertt___contents___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r validauthcertt ) (?t cert__attr__auth__contentst )
    (=
      (validauthcertt___contents___rcd_element
        (validauthcertt___contents___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t admintoken__interface__state__type )
    (=
      (statetype___admintoken__interface__state___rcd_element
        (statetype___admintoken__interface__state___rcd_update
          ?r
          ?t
        )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t valididcertt )
    (=
      (statetype___admintoken__interface__state___rcd_element
        (statetype___idcert___rcd_update ?r ?t )
      )
      (statetype___admintoken__interface__state___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t validauthcertt )
    (=
      (statetype___admintoken__interface__state___rcd_element
        (statetype___authcert___rcd_update ?r ?t )
      )
      (statetype___admintoken__interface__state___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___admintoken__interface__state___rcd_element
        (statetype___tokenid___rcd_update ?r ?t )
      )
      (statetype___admintoken__interface__state___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___admintoken__interface__state___rcd_element
        (statetype___tokentry___rcd_update ?r ?t )
      )
      (statetype___admintoken__interface__state___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___admintoken__interface__state___rcd_element
        (statetype___tokenpresence___rcd_update ?r ?t )
      )
      (statetype___admintoken__interface__state___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t admintoken__interface__state__type )
    (=
      (statetype___idcert___rcd_element
        (statetype___admintoken__interface__state___rcd_update
          ?r
          ?t
        )
      )
      (statetype___idcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t valididcertt )
    (=
      (statetype___idcert___rcd_element
        (statetype___idcert___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t validauthcertt )
    (=
      (statetype___idcert___rcd_element
        (statetype___authcert___rcd_update ?r ?t )
      )
      (statetype___idcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___idcert___rcd_element
        (statetype___tokenid___rcd_update ?r ?t )
      )
      (statetype___idcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___idcert___rcd_element
        (statetype___tokentry___rcd_update ?r ?t )
      )
      (statetype___idcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___idcert___rcd_element
        (statetype___tokenpresence___rcd_update ?r ?t )
      )
      (statetype___idcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t admintoken__interface__state__type )
    (=
      (statetype___authcert___rcd_element
        (statetype___admintoken__interface__state___rcd_update
          ?r
          ?t
        )
      )
      (statetype___authcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t valididcertt )
    (=
      (statetype___authcert___rcd_element
        (statetype___idcert___rcd_update ?r ?t )
      )
      (statetype___authcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t validauthcertt )
    (=
      (statetype___authcert___rcd_element
        (statetype___authcert___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___authcert___rcd_element
        (statetype___tokenid___rcd_update ?r ?t )
      )
      (statetype___authcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___authcert___rcd_element
        (statetype___tokentry___rcd_update ?r ?t )
      )
      (statetype___authcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___authcert___rcd_element
        (statetype___tokenpresence___rcd_update ?r ?t )
      )
      (statetype___authcert___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t admintoken__interface__state__type )
    (=
      (statetype___tokenid___rcd_element
        (statetype___admintoken__interface__state___rcd_update
          ?r
          ?t
        )
      )
      (statetype___tokenid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t valididcertt )
    (=
      (statetype___tokenid___rcd_element
        (statetype___idcert___rcd_update ?r ?t )
      )
      (statetype___tokenid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t validauthcertt )
    (=
      (statetype___tokenid___rcd_element
        (statetype___authcert___rcd_update ?r ?t )
      )
      (statetype___tokenid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokenid___rcd_element
        (statetype___tokenid___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokenid___rcd_element
        (statetype___tokentry___rcd_update ?r ?t )
      )
      (statetype___tokenid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokenid___rcd_element
        (statetype___tokenpresence___rcd_update ?r ?t )
      )
      (statetype___tokenid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t admintoken__interface__state__type )
    (=
      (statetype___tokentry___rcd_element
        (statetype___admintoken__interface__state___rcd_update
          ?r
          ?t
        )
      )
      (statetype___tokentry___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t valididcertt )
    (=
      (statetype___tokentry___rcd_element
        (statetype___idcert___rcd_update ?r ?t )
      )
      (statetype___tokentry___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t validauthcertt )
    (=
      (statetype___tokentry___rcd_element
        (statetype___authcert___rcd_update ?r ?t )
      )
      (statetype___tokentry___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokentry___rcd_element
        (statetype___tokenid___rcd_update ?r ?t )
      )
      (statetype___tokentry___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokentry___rcd_element
        (statetype___tokentry___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokentry___rcd_element
        (statetype___tokenpresence___rcd_update ?r ?t )
      )
      (statetype___tokentry___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t admintoken__interface__state__type )
    (=
      (statetype___tokenpresence___rcd_element
        (statetype___admintoken__interface__state___rcd_update
          ?r
          ?t
        )
      )
      (statetype___tokenpresence___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t valididcertt )
    (=
      (statetype___tokenpresence___rcd_element
        (statetype___idcert___rcd_update ?r ?t )
      )
      (statetype___tokenpresence___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t validauthcertt )
    (=
      (statetype___tokenpresence___rcd_element
        (statetype___authcert___rcd_update ?r ?t )
      )
      (statetype___tokenpresence___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokenpresence___rcd_element
        (statetype___tokenid___rcd_update ?r ?t )
      )
      (statetype___tokenpresence___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokenpresence___rcd_element
        (statetype___tokentry___rcd_update ?r ?t )
      )
      (statetype___tokenpresence___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r statetype ) (?t Int )
    (=
      (statetype___tokenpresence___rcd_element
        (statetype___tokenpresence___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (<= 0 tokenid )
    (<= tokenid 4294967295 )
    (<=
      tokentypes__notoken
      (admintoken__interface__thetokentry
        admintoken__interface__state
      )
    )
    (<=
      (admintoken__interface__thetokentry
        admintoken__interface__state
      )
      tokentypes__goodtoken
    )
    (=
      (cert__attr__auth__therole authcertcontents__1 )
      privtypes__useronly
    )
    (=
      (admintoken__interface__thetokentry
        admintoken__interface__state
      )
      tokentypes__goodtoken
    )
    (<=
      0
      (admintoken__interface__thetokenid
        admintoken__interface__state
      )
    )
    (<=
      (admintoken__interface__thetokenid
        admintoken__interface__state
      )
      4294967295
    )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 150 ) )
        (and
          (<= 0 (string___arr_element description__3 ?i___1 ) )
          (<= (string___arr_element description__3 ?i___1 ) 255 )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 150 ) )
        (and
          (<= 0 (string___arr_element description__4 ?i___1 ) )
          (<= (string___arr_element description__4 ?i___1 ) 255 )
        )
      )
    )
    (or (not idvalid__3 ) (not authvalid__4 ) )
    (<= 0 integer__size )
    (<= 0 character__size )
    (<= 0 positive__size )
    (<=
      basictypes__unsigned32t__base__first
      basictypes__unsigned32t__base__last
    )
    (<= 0 basictypes__presencet__size )
    (<= 0 audittypes__descriptioni__size )
    (<= 0 privtypes__privileget__size )
    (<= 0 privtypes__adminprivileget__size )
    (<= 0 tokentypes__tokenidt__size )
    (<=
      tokentypes__tokenidt__base__first
      tokentypes__tokenidt__base__last
    )
    (<= 0 tokentypes__tryt__size )
    (<= basictypes__unsigned32t__base__first 0 )
    (<= 4294967295 basictypes__unsigned32t__base__last )
    (<= tokentypes__tokenidt__base__first 0 )
    (<= 4294967295 tokentypes__tokenidt__base__last )
    (not
      (not
        (and
          idvalid__3
          (and
            authvalid__4
            (and
              (<=
                privtypes__guard
                (cert__attr__auth__therole authcertcontents__4 )
              )
              (<=
                (cert__attr__auth__therole authcertcontents__4 )
                privtypes__securityofficer
              )
            )
          )
        )
      )
    )
  )
  :status unknown
)
