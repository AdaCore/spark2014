(benchmark digest.19.1
  :logic AUFNIRA
  :extrasorts 
  ( string
    keystore__interface__digestpadt
    issystemt
    certtypes__rawdatat
    keystore__interface__digestt
    real___type
  )
  :extrafuns 
  ( (audittypes__admintokenexpired Int )
    (audittypes__admintokeninvalid Int )
    (audittypes__admintokenpresent Int )
    (audittypes__admintokenremoved Int )
    (audittypes__admintokenvalid Int )
    (audittypes__alarmraised Int )
    (audittypes__alarmsilenced Int )
    (audittypes__archivecheckfailed Int )
    (audittypes__archivecomplete Int )
    (audittypes__archivelog Int )
    (audittypes__auditalarmraised Int )
    (audittypes__auditalarmsilenced Int )
    (audittypes__authcertinvalid Int )
    (audittypes__authcertvalid Int )
    (audittypes__authcertwritefailed Int )
    (audittypes__authcertwritten Int )
    (audittypes__critical Int )
    (audittypes__descriptioni__base__first Int )
    (audittypes__descriptioni__base__last Int )
    (audittypes__descriptioni__first Int )
    (audittypes__descriptioni__last Int )
    (audittypes__descriptioni__size Int )
    (audittypes__displaychanged Int )
    (audittypes__doorclosed Int )
    (audittypes__dooropened Int )
    (audittypes__elementt__base__first Int )
    (audittypes__elementt__base__last Int )
    (audittypes__elementt__first Int )
    (audittypes__elementt__last Int )
    (audittypes__elementt__size Int )
    (audittypes__enrolmentcomplete Int )
    (audittypes__enrolmentfailed Int )
    (audittypes__entrydenied Int )
    (audittypes__entrypermitted Int )
    (audittypes__entrytimeout Int )
    (audittypes__fingerdetected Int )
    (audittypes__fingermatched Int )
    (audittypes__fingernotmatched Int )
    (audittypes__fingertimeout Int )
    (audittypes__information Int )
    (audittypes__invalidconfigdata Int )
    (audittypes__invalidoprequest Int )
    (audittypes__latchlocked Int )
    (audittypes__latchunlocked Int )
    (audittypes__operationstart Int )
    (audittypes__overridelock Int )
    (audittypes__screenchanged Int )
    (audittypes__severityt__base__first Int )
    (audittypes__severityt__base__last Int )
    (audittypes__severityt__first Int )
    (audittypes__severityt__last Int )
    (audittypes__severityt__size Int )
    (audittypes__shutdown Int )
    (audittypes__startenrolledtis Int )
    (audittypes__startunenrolledtis Int )
    (audittypes__systemfault Int )
    (audittypes__truncatelog Int )
    (audittypes__updatedconfigdata Int )
    (audittypes__usertokeninvalid Int )
    (audittypes__usertokenpresent Int )
    (audittypes__usertokenremoved Int )
    (audittypes__warning Int )
    (basictypes__bytet__base__first Int )
    (basictypes__bytet__base__last Int )
    (basictypes__bytet__first Int )
    (basictypes__bytet__last Int )
    (basictypes__bytet__size Int )
    (basictypes__unsigned32t__base__first Int )
    (basictypes__unsigned32t__base__last Int )
    (basictypes__unsigned32t__first Int )
    (basictypes__unsigned32t__last Int )
    (basictypes__unsigned32t__size Int )
    (bit___false Int )
    (bit___true Int )
    (bytesleft Int )
    (bytesleft___init Int )
    (bytesleft___loopinit Int )
    (certtypes__rawcertificatei__base__first Int )
    (certtypes__rawcertificatei__base__last Int )
    (certtypes__rawcertificatei__first Int )
    (certtypes__rawcertificatei__last Int )
    (certtypes__rawcertificatei__size Int )
    (certtypes__rawdatat___default_rcd certtypes__rawdatat )
    (certtypes__rawdatat__size Int )
    (character__base__first Int )
    (character__base__last Int )
    (character__first Int )
    (character__last Int )
    (character__size Int )
    (cryptotypes__algorithmt__base__first Int )
    (cryptotypes__algorithmt__base__last Int )
    (cryptotypes__algorithmt__first Int )
    (cryptotypes__algorithmt__last Int )
    (cryptotypes__algorithmt__size Int )
    (cryptotypes__md2 Int )
    (cryptotypes__md2_rsa Int )
    (cryptotypes__md5 Int )
    (cryptotypes__md5_rsa Int )
    (cryptotypes__ripemd128 Int )
    (cryptotypes__ripemd128_rsa Int )
    (cryptotypes__ripemd160 Int )
    (cryptotypes__ripemd160_rsa Int )
    (cryptotypes__rsa Int )
    (cryptotypes__sha1_rsa Int )
    (cryptotypes__sha_1 Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (issystem issystemt )
    (issystemt___default_arr issystemt )
    (issystemt___default_arr_element Int )
    (keystore__interface__argumentsbad Int )
    (keystore__interface__attributereadonly Int )
    (keystore__interface__attributetypeinvalid Int )
    (keystore__interface__attributevalueinvalid Int )
    (keystore__interface__buffertoosmall Int )
    (keystore__interface__cryptokialreadyinitialized Int )
    (keystore__interface__cryptokinotinitialized Int )
    (keystore__interface__datainvalid Int )
    (keystore__interface__datalenrange Int )
    (keystore__interface__deviceerror Int )
    (keystore__interface__devicememory Int )
    (keystore__interface__digestpadi__base__first Int )
    (keystore__interface__digestpadi__base__last Int )
    (keystore__interface__digestpadi__first Int )
    (keystore__interface__digestpadi__last Int )
    (keystore__interface__digestpadi__size Int )
    (keystore__interface__digestpadt___default_arr
      keystore__interface__digestpadt
    )
    (keystore__interface__digestpadt___default_arr_element Int )
    (keystore__interface__digestt___default_rcd
      keystore__interface__digestt
    )
    (keystore__interface__digestt__size Int )
    (keystore__interface__functioncanceled Int )
    (keystore__interface__functionfailed Int )
    (keystore__interface__generalerror Int )
    (keystore__interface__hostmemory Int )
    (keystore__interface__hundredbyteindext__base__first Int )
    (keystore__interface__hundredbyteindext__base__last Int )
    (keystore__interface__hundredbyteindext__first Int )
    (keystore__interface__hundredbyteindext__last Int )
    (keystore__interface__hundredbyteindext__size Int )
    (keystore__interface__keyfunctionnotpermitted Int )
    (keystore__interface__keyhandleinvalid Int )
    (keystore__interface__keysizerange Int )
    (keystore__interface__keytypeinconsistent Int )
    (keystore__interface__mechanisminvalid Int )
    (keystore__interface__mechanismparaminvalid Int )
    (keystore__interface__objecthandleinvalid Int )
    (keystore__interface__ok Int )
    (keystore__interface__operationactive Int )
    (keystore__interface__operationnotinitialized Int )
    (keystore__interface__returnvaluet__base__first Int )
    (keystore__interface__returnvaluet__base__last Int )
    (keystore__interface__returnvaluet__first Int )
    (keystore__interface__returnvaluet__last Int )
    (keystore__interface__returnvaluet__size Int )
    (keystore__interface__signatureinvalid Int )
    (keystore__interface__signaturelenrange Int )
    (keystore__interface__templateincomplete Int )
    (keystore__interface__templateinconsistent Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (loopmax Int )
    (loopmax___init Int )
    (loopmax___loopinit Int )
    (loopmax__entry__loop__1 Int )
    (loopmax__entry__loop__1___init Int )
    (loopmax__entry__loop__1___loopinit Int )
    (mechanism Int )
    (mechanism___init Int )
    (mechanism___loopinit Int )
    (null__string string )
    (positive__base__first Int )
    (positive__base__last Int )
    (positive__first Int )
    (positive__last Int )
    (positive__size Int )
    (rawcertdata certtypes__rawdatat )
    (rawcertdata___init certtypes__rawdatat )
    (rawcertdata___loopinit certtypes__rawdatat )
    (retvalfin Int )
    (retvalfin__3 Int )
    (retvalfin__3___init Int )
    (retvalfin__3___loopinit Int )
    (retvalfin___init Int )
    (retvalfin___loopinit Int )
    (retvalini Int )
    (retvalini__1 Int )
    (retvalini__1___init Int )
    (retvalini__1___loopinit Int )
    (retvalini___init Int )
    (retvalini___loopinit Int )
    (retvalupd Int )
    (retvalupd__2 Int )
    (retvalupd__2___init Int )
    (retvalupd__2___loopinit Int )
    (retvalupd___init Int )
    (retvalupd___loopinit Int )
    (size Int )
    (size___init Int )
    (size___loopinit Int )
    (string___default_arr string )
    (string___default_arr_element Int )
    (thedigest keystore__interface__digestt )
    (thedigest__3 keystore__interface__digestt )
    (thedigest__3___init keystore__interface__digestt )
    (thedigest__3___loopinit keystore__interface__digestt )
    (thedigest___init keystore__interface__digestt )
    (thedigest___loopinit keystore__interface__digestt )
    (audittypes__elementt___bit_eq Int Int Int )
    (audittypes__elementt__pos Int Int )
    (audittypes__elementt__pred Int Int )
    (audittypes__elementt__succ Int Int )
    (audittypes__elementt__val Int Int )
    (audittypes__severityt___bit_eq Int Int Int )
    (audittypes__severityt__pos Int Int )
    (audittypes__severityt__pred Int Int )
    (audittypes__severityt__succ Int Int )
    (audittypes__severityt__val Int Int )
    (basictypes__bytet___bit_eq Int Int Int )
    (basictypes__unsigned32t___bit_eq Int Int Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (bit__and Int Int Int )
    (bit__not Int Int Int )
    (bit__or Int Int Int )
    (bit__xor Int Int Int )
    (certtypes__rawdatat___bit_eq
      certtypes__rawdatat
      certtypes__rawdatat
      Int
    )
    (certtypes__rawdatat___datalength___rcd_element
      certtypes__rawdatat
      Int
    )
    (certtypes__rawdatat___datalength___rcd_update
      certtypes__rawdatat
      Int
      certtypes__rawdatat
    )
    (certtypes__rawdatat___rawdata___rcd_element
      certtypes__rawdatat
      string
    )
    (certtypes__rawdatat___rawdata___rcd_update
      certtypes__rawdatat
      string
      certtypes__rawdatat
    )
    (character___bit_eq Int Int Int )
    (character__pos Int Int )
    (character__val Int Int )
    (convertretvaltotext Int string string )
    (cryptotypes__algorithmt___bit_eq Int Int Int )
    (cryptotypes__algorithmt__pos Int Int )
    (cryptotypes__algorithmt__pred Int Int )
    (cryptotypes__algorithmt__succ Int Int )
    (cryptotypes__algorithmt__val Int Int )
    (getblock string Int Int string )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (issystemt___arr_element issystemt Int Int )
    (issystemt___arr_update issystemt Int Int issystemt )
    (issystemt___bit_eq issystemt issystemt Int )
    (issystemt___mk_const_arr Int issystemt )
    (keystore__interface__digestpadi___bit_eq Int Int Int )
    (keystore__interface__digestpadt___arr_element
      keystore__interface__digestpadt
      Int
      Int
    )
    (keystore__interface__digestpadt___arr_update
      keystore__interface__digestpadt
      Int
      Int
      keystore__interface__digestpadt
    )
    (keystore__interface__digestpadt___bit_eq
      keystore__interface__digestpadt
      keystore__interface__digestpadt
      Int
    )
    (keystore__interface__digestpadt___mk_const_arr
      Int
      keystore__interface__digestpadt
    )
    (keystore__interface__digestt___bit_eq
      keystore__interface__digestt
      keystore__interface__digestt
      Int
    )
    (keystore__interface__digestt___digestid___rcd_element
      keystore__interface__digestt
      Int
    )
    (keystore__interface__digestt___digestid___rcd_update
      keystore__interface__digestt
      Int
      keystore__interface__digestt
    )
    (keystore__interface__digestt___pad___rcd_element
      keystore__interface__digestt
      keystore__interface__digestpadt
    )
    (keystore__interface__digestt___pad___rcd_update
      keystore__interface__digestt
      keystore__interface__digestpadt
      keystore__interface__digestt
    )
    (keystore__interface__digestt___signreturn___rcd_element
      keystore__interface__digestt
      Int
    )
    (keystore__interface__digestt___signreturn___rcd_update
      keystore__interface__digestt
      Int
      keystore__interface__digestt
    )
    (keystore__interface__digestt___verifyreturn___rcd_element
      keystore__interface__digestt
      Int
    )
    (keystore__interface__digestt___verifyreturn___rcd_update
      keystore__interface__digestt
      Int
      keystore__interface__digestt
    )
    (keystore__interface__returnvaluet___bit_eq Int Int Int )
    (keystore__interface__returnvaluet__pos Int Int )
    (keystore__interface__returnvaluet__pred Int Int )
    (keystore__interface__returnvaluet__succ Int Int )
    (keystore__interface__returnvaluet__val Int Int )
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
  )
  :extrapreds 
  ( (audittypes__elementt__LE Int Int )
    (audittypes__elementt__LT Int Int )
    (audittypes__elementt___member Int )
    (audittypes__severityt__LE Int Int )
    (audittypes__severityt__LT Int Int )
    (audittypes__severityt___member Int )
    (bit___type___member Int )
    (cryptotypes__algorithmt__LE Int Int )
    (cryptotypes__algorithmt__LT Int Int )
    (cryptotypes__algorithmt___member Int )
    (int___odd Int )
    (issystemt___member issystemt )
    (keystore__interface__digestt___member
      keystore__interface__digestt
    )
    (keystore__interface__returnvaluet__LE Int Int )
    (keystore__interface__returnvaluet__LT Int Int )
    (keystore__interface__returnvaluet___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__elementt___member ?i )
      (= (audittypes__elementt__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__elementt___member ?i )
      (= (audittypes__elementt__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__elementt___member ?i )
      (implies
        (< ?i 43 )
        (= (audittypes__elementt__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__elementt___member ?i )
      (implies
        (< 0 ?i )
        (= (audittypes__elementt__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= audittypes__startunenrolledtis 0 )
  :assumption
  (= audittypes__startenrolledtis 1 )
  :assumption
  (= audittypes__enrolmentcomplete 2 )
  :assumption
  (= audittypes__enrolmentfailed 3 )
  :assumption
  (= audittypes__displaychanged 4 )
  :assumption
  (= audittypes__screenchanged 5 )
  :assumption
  (= audittypes__doorclosed 6 )
  :assumption
  (= audittypes__dooropened 7 )
  :assumption
  (= audittypes__latchlocked 8 )
  :assumption
  (= audittypes__latchunlocked 9 )
  :assumption
  (= audittypes__alarmraised 10 )
  :assumption
  (= audittypes__alarmsilenced 11 )
  :assumption
  (= audittypes__truncatelog 12 )
  :assumption
  (= audittypes__auditalarmraised 13 )
  :assumption
  (= audittypes__auditalarmsilenced 14 )
  :assumption
  (= audittypes__usertokenremoved 15 )
  :assumption
  (= audittypes__usertokenpresent 16 )
  :assumption
  (= audittypes__usertokeninvalid 17 )
  :assumption
  (= audittypes__authcertvalid 18 )
  :assumption
  (= audittypes__authcertinvalid 19 )
  :assumption
  (= audittypes__fingerdetected 20 )
  :assumption
  (= audittypes__fingertimeout 21 )
  :assumption
  (= audittypes__fingermatched 22 )
  :assumption
  (= audittypes__fingernotmatched 23 )
  :assumption
  (= audittypes__authcertwritten 24 )
  :assumption
  (= audittypes__authcertwritefailed 25 )
  :assumption
  (= audittypes__entrypermitted 26 )
  :assumption
  (= audittypes__entrytimeout 27 )
  :assumption
  (= audittypes__entrydenied 28 )
  :assumption
  (= audittypes__admintokenpresent 29 )
  :assumption
  (= audittypes__admintokenvalid 30 )
  :assumption
  (= audittypes__admintokeninvalid 31 )
  :assumption
  (= audittypes__admintokenexpired 32 )
  :assumption
  (= audittypes__admintokenremoved 33 )
  :assumption
  (= audittypes__invalidoprequest 34 )
  :assumption
  (= audittypes__operationstart 35 )
  :assumption
  (= audittypes__archivelog 36 )
  :assumption
  (= audittypes__archivecomplete 37 )
  :assumption
  (= audittypes__archivecheckfailed 38 )
  :assumption
  (= audittypes__updatedconfigdata 39 )
  :assumption
  (= audittypes__invalidconfigdata 40 )
  :assumption
  (= audittypes__shutdown 41 )
  :assumption
  (= audittypes__overridelock 42 )
  :assumption
  (= audittypes__systemfault 43 )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__severityt___member ?i )
      (= (audittypes__severityt__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__severityt___member ?i )
      (= (audittypes__severityt__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__severityt___member ?i )
      (implies
        (< ?i 2 )
        (= (audittypes__severityt__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (audittypes__severityt___member ?i )
      (implies
        (< 0 ?i )
        (= (audittypes__severityt__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= audittypes__information 0 )
  :assumption
  (= audittypes__warning 1 )
  :assumption
  (= audittypes__critical 2 )
  :assumption
  (forall
      (?i Int )
    (implies
      (cryptotypes__algorithmt___member ?i )
      (= (cryptotypes__algorithmt__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (cryptotypes__algorithmt___member ?i )
      (= (cryptotypes__algorithmt__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (cryptotypes__algorithmt___member ?i )
      (implies
        (< ?i 10 )
        (= (cryptotypes__algorithmt__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (cryptotypes__algorithmt___member ?i )
      (implies
        (< 0 ?i )
        (= (cryptotypes__algorithmt__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= cryptotypes__rsa 0 )
  :assumption
  (= cryptotypes__md2 1 )
  :assumption
  (= cryptotypes__md5 2 )
  :assumption
  (= cryptotypes__sha_1 3 )
  :assumption
  (= cryptotypes__ripemd128 4 )
  :assumption
  (= cryptotypes__ripemd160 5 )
  :assumption
  (= cryptotypes__md2_rsa 6 )
  :assumption
  (= cryptotypes__md5_rsa 7 )
  :assumption
  (= cryptotypes__sha1_rsa 8 )
  :assumption
  (= cryptotypes__ripemd128_rsa 9 )
  :assumption
  (= cryptotypes__ripemd160_rsa 10 )
  :assumption
  (forall
      (?i Int )
    (implies
      (keystore__interface__returnvaluet___member ?i )
      (= (keystore__interface__returnvaluet__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (keystore__interface__returnvaluet___member ?i )
      (= (keystore__interface__returnvaluet__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (keystore__interface__returnvaluet___member ?i )
      (implies
        (< ?i 28 )
        (= (keystore__interface__returnvaluet__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (keystore__interface__returnvaluet___member ?i )
      (implies
        (< 0 ?i )
        (= (keystore__interface__returnvaluet__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= keystore__interface__ok 0 )
  :assumption
  (= keystore__interface__hostmemory 1 )
  :assumption
  (= keystore__interface__generalerror 2 )
  :assumption
  (= keystore__interface__functionfailed 3 )
  :assumption
  (= keystore__interface__argumentsbad 4 )
  :assumption
  (= keystore__interface__attributereadonly 5 )
  :assumption
  (= keystore__interface__attributetypeinvalid 6 )
  :assumption
  (= keystore__interface__attributevalueinvalid 7 )
  :assumption
  (= keystore__interface__datainvalid 8 )
  :assumption
  (= keystore__interface__datalenrange 9 )
  :assumption
  (= keystore__interface__deviceerror 10 )
  :assumption
  (= keystore__interface__devicememory 11 )
  :assumption
  (= keystore__interface__functioncanceled 12 )
  :assumption
  (= keystore__interface__keyhandleinvalid 13 )
  :assumption
  (= keystore__interface__keysizerange 14 )
  :assumption
  (= keystore__interface__keytypeinconsistent 15 )
  :assumption
  (= keystore__interface__keyfunctionnotpermitted 16 )
  :assumption
  (= keystore__interface__mechanisminvalid 17 )
  :assumption
  (= keystore__interface__mechanismparaminvalid 18 )
  :assumption
  (= keystore__interface__objecthandleinvalid 19 )
  :assumption
  (= keystore__interface__operationactive 20 )
  :assumption
  (= keystore__interface__operationnotinitialized 21 )
  :assumption
  (= keystore__interface__signatureinvalid 22 )
  :assumption
  (= keystore__interface__signaturelenrange 23 )
  :assumption
  (= keystore__interface__templateincomplete 24 )
  :assumption
  (= keystore__interface__templateinconsistent 25 )
  :assumption
  (= keystore__interface__buffertoosmall 26 )
  :assumption
  (= keystore__interface__cryptokinotinitialized 27 )
  :assumption
  (= keystore__interface__cryptokialreadyinitialized 28 )
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
  (<= 0 basictypes__bytet__size )
  :assumption
  (= basictypes__bytet__size 8 )
  :assumption
  (= basictypes__bytet__first 0 )
  :assumption
  (= basictypes__bytet__last 255 )
  :assumption
  (<=
    basictypes__bytet__base__first
    basictypes__bytet__base__last
  )
  :assumption
  (<=
    basictypes__bytet__base__first
    basictypes__bytet__first
  )
  :assumption
  (<= basictypes__bytet__last basictypes__bytet__base__last )
  :assumption
  (<= 0 audittypes__elementt__size )
  :assumption
  (=
    audittypes__elementt__first
    audittypes__startunenrolledtis
  )
  :assumption
  (= audittypes__elementt__last audittypes__systemfault )
  :assumption
  (=
    audittypes__elementt__base__first
    audittypes__startunenrolledtis
  )
  :assumption
  (=
    audittypes__elementt__base__last
    audittypes__systemfault
  )
  :assumption
  (<= 0 audittypes__severityt__size )
  :assumption
  (= audittypes__severityt__first audittypes__information )
  :assumption
  (= audittypes__severityt__last audittypes__critical )
  :assumption
  (=
    audittypes__severityt__base__first
    audittypes__information
  )
  :assumption
  (= audittypes__severityt__base__last audittypes__critical )
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
  (<= 0 cryptotypes__algorithmt__size )
  :assumption
  (= cryptotypes__algorithmt__first cryptotypes__rsa )
  :assumption
  (=
    cryptotypes__algorithmt__last
    cryptotypes__ripemd160_rsa
  )
  :assumption
  (= cryptotypes__algorithmt__base__first cryptotypes__rsa )
  :assumption
  (=
    cryptotypes__algorithmt__base__last
    cryptotypes__ripemd160_rsa
  )
  :assumption
  (<= 0 certtypes__rawcertificatei__size )
  :assumption
  (= certtypes__rawcertificatei__first 1 )
  :assumption
  (= certtypes__rawcertificatei__last 4096 )
  :assumption
  (= certtypes__rawcertificatei__base__first (~ 2147483648 ) )
  :assumption
  (= certtypes__rawcertificatei__base__last 2147483647 )
  :assumption
  (<= 0 keystore__interface__hundredbyteindext__size )
  :assumption
  (= keystore__interface__hundredbyteindext__first 1 )
  :assumption
  (= keystore__interface__hundredbyteindext__last 100 )
  :assumption
  (=
    keystore__interface__hundredbyteindext__base__first
    (~ 2147483648 )
  )
  :assumption
  (=
    keystore__interface__hundredbyteindext__base__last
    2147483647
  )
  :assumption
  (<= 0 keystore__interface__returnvaluet__size )
  :assumption
  (=
    keystore__interface__returnvaluet__first
    keystore__interface__ok
  )
  :assumption
  (=
    keystore__interface__returnvaluet__last
    keystore__interface__cryptokialreadyinitialized
  )
  :assumption
  (=
    keystore__interface__returnvaluet__base__first
    keystore__interface__ok
  )
  :assumption
  (=
    keystore__interface__returnvaluet__base__last
    keystore__interface__cryptokialreadyinitialized
  )
  :assumption
  (<= 0 keystore__interface__digestpadi__size )
  :assumption
  (= keystore__interface__digestpadi__first 1 )
  :assumption
  (= keystore__interface__digestpadi__last 20 )
  :assumption
  (<=
    keystore__interface__digestpadi__base__first
    keystore__interface__digestpadi__base__last
  )
  :assumption
  (<=
    keystore__interface__digestpadi__base__first
    keystore__interface__digestpadi__first
  )
  :assumption
  (<=
    keystore__interface__digestpadi__last
    keystore__interface__digestpadi__base__last
  )
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
  (audittypes__elementt___member
    audittypes__admintokenexpired
  )
  :assumption
  (audittypes__elementt___member
    audittypes__admintokeninvalid
  )
  :assumption
  (audittypes__elementt___member
    audittypes__admintokenpresent
  )
  :assumption
  (audittypes__elementt___member
    audittypes__admintokenremoved
  )
  :assumption
  (audittypes__elementt___member audittypes__admintokenvalid )
  :assumption
  (audittypes__elementt___member audittypes__alarmraised )
  :assumption
  (audittypes__elementt___member audittypes__alarmsilenced )
  :assumption
  (audittypes__elementt___member
    audittypes__archivecheckfailed
  )
  :assumption
  (audittypes__elementt___member audittypes__archivecomplete )
  :assumption
  (audittypes__elementt___member audittypes__archivelog )
  :assumption
  (audittypes__elementt___member
    audittypes__auditalarmraised
  )
  :assumption
  (audittypes__elementt___member
    audittypes__auditalarmsilenced
  )
  :assumption
  (audittypes__elementt___member audittypes__authcertinvalid )
  :assumption
  (audittypes__elementt___member audittypes__authcertvalid )
  :assumption
  (audittypes__elementt___member
    audittypes__authcertwritefailed
  )
  :assumption
  (audittypes__elementt___member audittypes__authcertwritten )
  :assumption
  (audittypes__severityt___member audittypes__critical )
  :assumption
  (audittypes__elementt___member audittypes__displaychanged )
  :assumption
  (audittypes__elementt___member audittypes__doorclosed )
  :assumption
  (audittypes__elementt___member audittypes__dooropened )
  :assumption
  (audittypes__elementt___member
    audittypes__elementt__base__first
  )
  :assumption
  (audittypes__elementt___member
    audittypes__elementt__base__last
  )
  :assumption
  (audittypes__elementt___member audittypes__elementt__first )
  :assumption
  (audittypes__elementt___member audittypes__elementt__last )
  :assumption
  (audittypes__elementt___member
    audittypes__enrolmentcomplete
  )
  :assumption
  (audittypes__elementt___member audittypes__enrolmentfailed )
  :assumption
  (audittypes__elementt___member audittypes__entrydenied )
  :assumption
  (audittypes__elementt___member audittypes__entrypermitted )
  :assumption
  (audittypes__elementt___member audittypes__entrytimeout )
  :assumption
  (audittypes__elementt___member audittypes__fingerdetected )
  :assumption
  (audittypes__elementt___member audittypes__fingermatched )
  :assumption
  (audittypes__elementt___member
    audittypes__fingernotmatched
  )
  :assumption
  (audittypes__elementt___member audittypes__fingertimeout )
  :assumption
  (audittypes__severityt___member audittypes__information )
  :assumption
  (audittypes__elementt___member
    audittypes__invalidconfigdata
  )
  :assumption
  (audittypes__elementt___member
    audittypes__invalidoprequest
  )
  :assumption
  (audittypes__elementt___member audittypes__latchlocked )
  :assumption
  (audittypes__elementt___member audittypes__latchunlocked )
  :assumption
  (audittypes__elementt___member audittypes__operationstart )
  :assumption
  (audittypes__elementt___member audittypes__overridelock )
  :assumption
  (audittypes__elementt___member audittypes__screenchanged )
  :assumption
  (audittypes__severityt___member
    audittypes__severityt__base__first
  )
  :assumption
  (audittypes__severityt___member
    audittypes__severityt__base__last
  )
  :assumption
  (audittypes__severityt___member
    audittypes__severityt__first
  )
  :assumption
  (audittypes__severityt___member
    audittypes__severityt__last
  )
  :assumption
  (audittypes__elementt___member audittypes__shutdown )
  :assumption
  (audittypes__elementt___member
    audittypes__startenrolledtis
  )
  :assumption
  (audittypes__elementt___member
    audittypes__startunenrolledtis
  )
  :assumption
  (audittypes__elementt___member audittypes__systemfault )
  :assumption
  (audittypes__elementt___member audittypes__truncatelog )
  :assumption
  (audittypes__elementt___member
    audittypes__updatedconfigdata
  )
  :assumption
  (audittypes__elementt___member
    audittypes__usertokeninvalid
  )
  :assumption
  (audittypes__elementt___member
    audittypes__usertokenpresent
  )
  :assumption
  (audittypes__elementt___member
    audittypes__usertokenremoved
  )
  :assumption
  (audittypes__severityt___member audittypes__warning )
  :assumption
  (cryptotypes__algorithmt___member
    cryptotypes__algorithmt__base__first
  )
  :assumption
  (cryptotypes__algorithmt___member
    cryptotypes__algorithmt__base__last
  )
  :assumption
  (cryptotypes__algorithmt___member
    cryptotypes__algorithmt__first
  )
  :assumption
  (cryptotypes__algorithmt___member
    cryptotypes__algorithmt__last
  )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__md2 )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__md2_rsa )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__md5 )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__md5_rsa )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__ripemd128 )
  :assumption
  (cryptotypes__algorithmt___member
    cryptotypes__ripemd128_rsa
  )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__ripemd160 )
  :assumption
  (cryptotypes__algorithmt___member
    cryptotypes__ripemd160_rsa
  )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__rsa )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__sha1_rsa )
  :assumption
  (cryptotypes__algorithmt___member cryptotypes__sha_1 )
  :assumption
  (issystemt___member issystem )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__argumentsbad
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__attributereadonly
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__attributetypeinvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__attributevalueinvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__buffertoosmall
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__cryptokialreadyinitialized
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__cryptokinotinitialized
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__datainvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__datalenrange
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__deviceerror
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__devicememory
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__functioncanceled
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__functionfailed
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__generalerror
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__hostmemory
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__keyfunctionnotpermitted
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__keyhandleinvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__keysizerange
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__keytypeinconsistent
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__mechanisminvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__mechanismparaminvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__objecthandleinvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__ok
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__operationactive
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__operationnotinitialized
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__returnvaluet__base__first
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__returnvaluet__base__last
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__returnvaluet__first
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__returnvaluet__last
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__signatureinvalid
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__signaturelenrange
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__templateincomplete
  )
  :assumption
  (keystore__interface__returnvaluet___member
    keystore__interface__templateinconsistent
  )
  :assumption
  (cryptotypes__algorithmt___member mechanism )
  :assumption
  (cryptotypes__algorithmt___member mechanism___init )
  :assumption
  (cryptotypes__algorithmt___member mechanism___loopinit )
  :assumption
  (keystore__interface__returnvaluet___member retvalfin )
  :assumption
  (keystore__interface__returnvaluet___member retvalfin__3 )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalfin__3___init
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalfin__3___loopinit
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalfin___init
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalfin___loopinit
  )
  :assumption
  (keystore__interface__returnvaluet___member retvalini )
  :assumption
  (keystore__interface__returnvaluet___member retvalini__1 )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalini__1___init
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalini__1___loopinit
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalini___init
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalini___loopinit
  )
  :assumption
  (keystore__interface__returnvaluet___member retvalupd )
  :assumption
  (keystore__interface__returnvaluet___member retvalupd__2 )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalupd__2___init
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalupd__2___loopinit
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalupd___init
  )
  :assumption
  (keystore__interface__returnvaluet___member
    retvalupd___loopinit
  )
  :assumption
  (keystore__interface__digestt___member thedigest )
  :assumption
  (keystore__interface__digestt___member thedigest__3 )
  :assumption
  (keystore__interface__digestt___member thedigest__3___init )
  :assumption
  (keystore__interface__digestt___member
    thedigest__3___loopinit
  )
  :assumption
  (keystore__interface__digestt___member thedigest___init )
  :assumption
  (keystore__interface__digestt___member
    thedigest___loopinit
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (audittypes__elementt___member ?x0 )
      (audittypes__elementt___member
        (audittypes__elementt__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (audittypes__elementt___member ?x0 )
      (audittypes__elementt___member
        (audittypes__elementt__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (audittypes__elementt___member
      (audittypes__elementt__val ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (audittypes__severityt___member ?x0 )
      (audittypes__severityt___member
        (audittypes__severityt__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (audittypes__severityt___member ?x0 )
      (audittypes__severityt___member
        (audittypes__severityt__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (audittypes__severityt___member
      (audittypes__severityt__val ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (cryptotypes__algorithmt___member ?x0 )
      (cryptotypes__algorithmt___member
        (cryptotypes__algorithmt__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (cryptotypes__algorithmt___member ?x0 )
      (cryptotypes__algorithmt___member
        (cryptotypes__algorithmt__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (cryptotypes__algorithmt___member
      (cryptotypes__algorithmt__val ?x0 )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (keystore__interface__returnvaluet___member ?x0 )
      (keystore__interface__returnvaluet___member
        (keystore__interface__returnvaluet__pred ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (keystore__interface__returnvaluet___member ?x0 )
      (keystore__interface__returnvaluet___member
        (keystore__interface__returnvaluet__succ ?x0 )
      )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (keystore__interface__returnvaluet___member
      (keystore__interface__returnvaluet__val ?x0 )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (audittypes__elementt___member ?x )
      (and (<= 0 ?x ) (<= ?x 43 ) )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (audittypes__severityt___member ?x )
      (and (<= 0 ?x ) (<= ?x 2 ) )
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
      (cryptotypes__algorithmt___member ?x )
      (and (<= 0 ?x ) (<= ?x 10 ) )
    )
  )
  :assumption
  (forall
      (?x issystemt )
    (iff
      (issystemt___member ?x )
      (forall
          (?s0 Int )
        (and
          (implies
            (keystore__interface__returnvaluet___member ?s0 )
            (bit___type___member (issystemt___arr_element ?x ?s0 ) )
          )
          (implies
            (not (keystore__interface__returnvaluet___member ?s0 ) )
            (=
              (issystemt___arr_element ?x ?s0 )
              issystemt___default_arr_element
            )
          )
        )
      )
    )
  )
  :assumption
  (forall
      (?x keystore__interface__digestt )
    (iff
      (keystore__interface__digestt___member ?x )
      (and
        true
        (keystore__interface__returnvaluet___member
          (keystore__interface__digestt___signreturn___rcd_element
            ?x
          )
        )
        (keystore__interface__returnvaluet___member
          (keystore__interface__digestt___verifyreturn___rcd_element
            ?x
          )
        )
        true
      )
    )
  )
  :assumption
  (forall
      (?x Int )
    (iff
      (keystore__interface__returnvaluet___member ?x )
      (and (<= 0 ?x ) (<= ?x 28 ) )
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
    (iff
      (= (audittypes__elementt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (audittypes__severityt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (basictypes__bytet___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (basictypes__unsigned32t___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x certtypes__rawdatat ) (?y certtypes__rawdatat )
    (iff
      (= (certtypes__rawdatat___bit_eq ?x ?y ) bit___true )
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
      (?x Int ) (?y Int )
    (iff
      (= (cryptotypes__algorithmt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x issystemt ) (?y issystemt )
    (iff
      (= (issystemt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (=
        (keystore__interface__digestpadi___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x keystore__interface__digestpadt )
      (?y keystore__interface__digestpadt )
    (iff
      (=
        (keystore__interface__digestpadt___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x keystore__interface__digestt )
      (?y keystore__interface__digestt )
    (iff
      (=
        (keystore__interface__digestt___bit_eq ?x ?y )
        bit___true
      )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (=
        (keystore__interface__returnvaluet___bit_eq ?x ?y )
        bit___true
      )
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
      (keystore__interface__digestpadt___arr_element
        (keystore__interface__digestpadt___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v Int )
    (=
      (issystemt___arr_element
        (issystemt___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a issystemt ) (?s0 Int ) (?t Int )
    (=
      (issystemt___arr_element
        (issystemt___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a issystemt ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (issystemt___arr_element
          (issystemt___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (issystemt___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a keystore__interface__digestpadt ) (?s0 Int ) (?t Int )
    (=
      (keystore__interface__digestpadt___arr_element
        (keystore__interface__digestpadt___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a keystore__interface__digestpadt )
      (?s0 Int )
      (?s0p Int )
      (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (keystore__interface__digestpadt___arr_element
          (keystore__interface__digestpadt___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (keystore__interface__digestpadt___arr_element ?a ?s0p )
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
      (?r certtypes__rawdatat ) (?t string )
    (=
      (certtypes__rawdatat___rawdata___rcd_element
        (certtypes__rawdatat___rawdata___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r certtypes__rawdatat ) (?t Int )
    (=
      (certtypes__rawdatat___rawdata___rcd_element
        (certtypes__rawdatat___datalength___rcd_update ?r ?t )
      )
      (certtypes__rawdatat___rawdata___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r certtypes__rawdatat ) (?t string )
    (=
      (certtypes__rawdatat___datalength___rcd_element
        (certtypes__rawdatat___rawdata___rcd_update ?r ?t )
      )
      (certtypes__rawdatat___datalength___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r certtypes__rawdatat ) (?t Int )
    (=
      (certtypes__rawdatat___datalength___rcd_element
        (certtypes__rawdatat___datalength___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___digestid___rcd_element
        (keystore__interface__digestt___digestid___rcd_update
          ?r
          ?t
        )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___digestid___rcd_element
        (keystore__interface__digestt___signreturn___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___digestid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___digestid___rcd_element
        (keystore__interface__digestt___verifyreturn___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___digestid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt )
      (?t keystore__interface__digestpadt )
    (=
      (keystore__interface__digestt___digestid___rcd_element
        (keystore__interface__digestt___pad___rcd_update ?r ?t )
      )
      (keystore__interface__digestt___digestid___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___signreturn___rcd_element
        (keystore__interface__digestt___digestid___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___signreturn___rcd_element
        ?r
      )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___signreturn___rcd_element
        (keystore__interface__digestt___signreturn___rcd_update
          ?r
          ?t
        )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___signreturn___rcd_element
        (keystore__interface__digestt___verifyreturn___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___signreturn___rcd_element
        ?r
      )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt )
      (?t keystore__interface__digestpadt )
    (=
      (keystore__interface__digestt___signreturn___rcd_element
        (keystore__interface__digestt___pad___rcd_update ?r ?t )
      )
      (keystore__interface__digestt___signreturn___rcd_element
        ?r
      )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___verifyreturn___rcd_element
        (keystore__interface__digestt___digestid___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___verifyreturn___rcd_element
        ?r
      )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___verifyreturn___rcd_element
        (keystore__interface__digestt___signreturn___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___verifyreturn___rcd_element
        ?r
      )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___verifyreturn___rcd_element
        (keystore__interface__digestt___verifyreturn___rcd_update
          ?r
          ?t
        )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt )
      (?t keystore__interface__digestpadt )
    (=
      (keystore__interface__digestt___verifyreturn___rcd_element
        (keystore__interface__digestt___pad___rcd_update ?r ?t )
      )
      (keystore__interface__digestt___verifyreturn___rcd_element
        ?r
      )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___pad___rcd_element
        (keystore__interface__digestt___digestid___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___pad___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___pad___rcd_element
        (keystore__interface__digestt___signreturn___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___pad___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt ) (?t Int )
    (=
      (keystore__interface__digestt___pad___rcd_element
        (keystore__interface__digestt___verifyreturn___rcd_update
          ?r
          ?t
        )
      )
      (keystore__interface__digestt___pad___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r keystore__interface__digestt )
      (?t keystore__interface__digestpadt )
    (=
      (keystore__interface__digestt___pad___rcd_element
        (keystore__interface__digestt___pad___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (<=
      (int___div
        (-
          (certtypes__rawdatat___datalength___rcd_element
            rawcertdata
          )
          1
        )
        100
      )
      40
    )
    (<= 1 loop__1__i )
    (implies
      (<=
        (-
          (certtypes__rawdatat___datalength___rcd_element
            rawcertdata
          )
          (* (- loop__1__i 1 ) 100 )
        )
        100
      )
      (=
        loop__1__i
        (+
          (int___div
            (-
              (certtypes__rawdatat___datalength___rcd_element
                rawcertdata
              )
              1
            )
            100
          )
          1
        )
      )
    )
    (implies
      (= loop__1__i 41 )
      (<=
        (-
          (certtypes__rawdatat___datalength___rcd_element
            rawcertdata
          )
          (* (- loop__1__i 1 ) 100 )
        )
        96
      )
    )
    (<=
      1
      (certtypes__rawdatat___datalength___rcd_element
        rawcertdata
      )
    )
    (<=
      (certtypes__rawdatat___datalength___rcd_element
        rawcertdata
      )
      4096
    )
    (<= 1 size )
    (<= size 100 )
    (<= cryptotypes__rsa mechanism )
    (<= mechanism cryptotypes__ripemd160_rsa )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 4096 ) )
        (and
          (<=
            0
            (string___arr_element
              (certtypes__rawdatat___rawdata___rcd_element rawcertdata )
              ?i___1
            )
          )
          (<=
            (string___arr_element
              (certtypes__rawdatat___rawdata___rcd_element rawcertdata )
              ?i___1
            )
            255
          )
        )
      )
    )
    (<=
      0
      (int___div
        (-
          (certtypes__rawdatat___datalength___rcd_element
            rawcertdata
          )
          1
        )
        100
      )
    )
    (<=
      (-
        (certtypes__rawdatat___datalength___rcd_element
          rawcertdata
        )
        (* (- loop__1__i 1 ) 100 )
      )
      2147483647
    )
    (<=
      100
      (-
        (certtypes__rawdatat___datalength___rcd_element
          rawcertdata
        )
        (* (- loop__1__i 1 ) 100 )
      )
    )
    (<= (+ size (* (- loop__1__i 1 ) 100 ) ) 4096 )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 100 ) )
        (and
          (<=
            0
            (string___arr_element
              (getblock
                (certtypes__rawdatat___rawdata___rcd_element rawcertdata )
                loop__1__i
                size
              )
              ?i___1
            )
          )
          (<=
            (string___arr_element
              (getblock
                (certtypes__rawdatat___rawdata___rcd_element rawcertdata )
                loop__1__i
                size
              )
              ?i___1
            )
            255
          )
        )
      )
    )
    (<
      loop__1__i
      (+
        (int___div
          (-
            (certtypes__rawdatat___datalength___rcd_element
              rawcertdata
            )
            1
          )
          100
        )
        1
      )
    )
    (<= 0 integer__size )
    (<= 0 character__size )
    (<= 0 positive__size )
    (<=
      basictypes__unsigned32t__base__first
      basictypes__unsigned32t__base__last
    )
    (<=
      basictypes__bytet__base__first
      basictypes__bytet__base__last
    )
    (<= 0 audittypes__elementt__size )
    (<= 0 audittypes__severityt__size )
    (<= 0 audittypes__descriptioni__size )
    (<= 0 cryptotypes__algorithmt__size )
    (<= 0 certtypes__rawcertificatei__size )
    (<= 0 keystore__interface__hundredbyteindext__size )
    (<= 0 keystore__interface__returnvaluet__size )
    (<= 0 keystore__interface__digestpadi__size )
    (<=
      keystore__interface__digestpadi__base__first
      keystore__interface__digestpadi__base__last
    )
    (<= basictypes__unsigned32t__base__first 0 )
    (<= 4294967295 basictypes__unsigned32t__base__last )
    (<= basictypes__bytet__base__first 0 )
    (<= 255 basictypes__bytet__base__last )
    (<= keystore__interface__digestpadi__base__first 1 )
    (<= 20 keystore__interface__digestpadi__base__last )
    (not
      (not
        (=
          (-
            (certtypes__rawdatat___datalength___rcd_element
              rawcertdata
            )
            (* (- loop__1__i 1 ) 100 )
          )
          100
        )
      )
    )
  )
  :status unknown
)
