(benchmark addelementtologfilewithtruncatechecks.6.1
  :logic AUFNIRA
  :extrasorts 
  ( string
    logfilesstatust
    logfilelistentriest
    logfileentryt
    logfilelistt
    real___type
  )
  :extrafuns 
  ( (alarmtypes__alarming Int )
    (alarmtypes__silent Int )
    (alarmtypes__statust__base__first Int )
    (alarmtypes__statust__base__last Int )
    (alarmtypes__statust__first Int )
    (alarmtypes__statust__last Int )
    (alarmtypes__statust__size Int )
    (archived Int )
    (auditalarm Int )
    (auditalarm__1 Int )
    (auditalarm__1___init Int )
    (auditalarm__1___loopinit Int )
    (auditalarm___init Int )
    (auditalarm___loopinit Int )
    (audittypes__admintokenexpired Int )
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
    (audittypes__usertexti__base__first Int )
    (audittypes__usertexti__base__last Int )
    (audittypes__usertexti__first Int )
    (audittypes__usertexti__last Int )
    (audittypes__usertexti__size Int )
    (audittypes__usertokeninvalid Int )
    (audittypes__usertokenpresent Int )
    (audittypes__usertokenremoved Int )
    (audittypes__warning Int )
    (bit___false Int )
    (bit___true Int )
    (character__base__first Int )
    (character__base__last Int )
    (character__first Int )
    (character__last Int )
    (character__size Int )
    (currentlogfile Int )
    (currentlogfile__2 Int )
    (currentlogfile__2___init Int )
    (currentlogfile__2___loopinit Int )
    (currentlogfile__3 Int )
    (currentlogfile__3___init Int )
    (currentlogfile__3___loopinit Int )
    (currentlogfile___init Int )
    (currentlogfile___loopinit Int )
    (description string )
    (description___init string )
    (description___loopinit string )
    (elementid Int )
    (elementid___init Int )
    (elementid___loopinit Int )
    (fileentrycountt__base__first Int )
    (fileentrycountt__base__last Int )
    (fileentrycountt__first Int )
    (fileentrycountt__last Int )
    (fileentrycountt__size Int )
    (filestatust__base__first Int )
    (filestatust__base__last Int )
    (filestatust__first Int )
    (filestatust__last Int )
    (filestatust__size Int )
    (free Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (logentrycountt__base__first Int )
    (logentrycountt__base__last Int )
    (logentrycountt__first Int )
    (logentrycountt__last Int )
    (logentrycountt__size Int )
    (logfilecountt__base__first Int )
    (logfilecountt__base__last Int )
    (logfilecountt__first Int )
    (logfilecountt__last Int )
    (logfilecountt__size Int )
    (logfileentries logfileentryt )
    (logfileentries__1 logfileentryt )
    (logfileentries__1___init logfileentryt )
    (logfileentries__1___loopinit logfileentryt )
    (logfileentries__2 logfileentryt )
    (logfileentries__2___init logfileentryt )
    (logfileentries__2___loopinit logfileentryt )
    (logfileentries__3 logfileentryt )
    (logfileentries__3___init logfileentryt )
    (logfileentries__3___loopinit logfileentryt )
    (logfileentries___init logfileentryt )
    (logfileentries___loopinit logfileentryt )
    (logfileentryt___default_arr logfileentryt )
    (logfileentryt___default_arr_element Int )
    (logfileindext__base__first Int )
    (logfileindext__base__last Int )
    (logfileindext__first Int )
    (logfileindext__last Int )
    (logfileindext__size Int )
    (logfilelistentriest___default_arr logfilelistentriest )
    (logfilelistentriest___default_arr_element Int )
    (logfilelistt___default_rcd logfilelistt )
    (logfilelistt__size Int )
    (logfilesstatus logfilesstatust )
    (logfilesstatus__1 logfilesstatust )
    (logfilesstatus__1___init logfilesstatust )
    (logfilesstatus__1___loopinit logfilesstatust )
    (logfilesstatus__2 logfilesstatust )
    (logfilesstatus__2___init logfilesstatust )
    (logfilesstatus__2___loopinit logfilesstatust )
    (logfilesstatus__3 logfilesstatust )
    (logfilesstatus__3___init logfilesstatust )
    (logfilesstatus__3___loopinit logfilesstatust )
    (logfilesstatus___init logfilesstatust )
    (logfilesstatus___loopinit logfilesstatust )
    (logfilesstatust___default_arr logfilesstatust )
    (logfilesstatust___default_arr_element Int )
    (maxlogentries Int )
    (maxlogfileentries Int )
    (null__string string )
    (numberlogentries Int )
    (numberlogentries__1 Int )
    (numberlogentries__1___init Int )
    (numberlogentries__1___loopinit Int )
    (numberlogentries__2 Int )
    (numberlogentries__2___init Int )
    (numberlogentries__2___loopinit Int )
    (numberlogentries__3 Int )
    (numberlogentries__3___init Int )
    (numberlogentries__3___loopinit Int )
    (numberlogentries___init Int )
    (numberlogentries___loopinit Int )
    (positive__base__first Int )
    (positive__base__last Int )
    (positive__first Int )
    (positive__last Int )
    (positive__size Int )
    (severity Int )
    (severity___init Int )
    (severity___loopinit Int )
    (string___default_arr string )
    (string___default_arr_element Int )
    (truncatedescription string )
    (truncatedescription__1 string )
    (truncatedescription__1___init string )
    (truncatedescription__1___loopinit string )
    (truncatedescription___init string )
    (truncatedescription___loopinit string )
    (used Int )
    (usedlogfiles logfilelistt )
    (usedlogfiles__1 logfilelistt )
    (usedlogfiles__1___init logfilelistt )
    (usedlogfiles__1___loopinit logfilelistt )
    (usedlogfiles__2 logfilelistt )
    (usedlogfiles__2___init logfilelistt )
    (usedlogfiles__2___loopinit logfilelistt )
    (usedlogfiles__3 logfilelistt )
    (usedlogfiles__3___init logfilelistt )
    (usedlogfiles__3___loopinit logfilelistt )
    (usedlogfiles___init logfilelistt )
    (usedlogfiles___loopinit logfilelistt )
    (user string )
    (user___init string )
    (user___loopinit string )
    (alarmtypes__statust___bit_eq Int Int Int )
    (alarmtypes__statust__pos Int Int )
    (alarmtypes__statust__pred Int Int )
    (alarmtypes__statust__succ Int Int )
    (alarmtypes__statust__val Int Int )
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
    (filestatust___bit_eq Int Int Int )
    (filestatust__pos Int Int )
    (filestatust__pred Int Int )
    (filestatust__succ Int Int )
    (filestatust__val Int Int )
    (int___abs Int Int )
    (int___div Int Int Int )
    (int___exp Int Int Int )
    (int___mod Int Int Int )
    (int___rem Int Int Int )
    (int___times Int Int Int )
    (int___to_real Int real___type )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (logentrycountt___bit_eq Int Int Int )
    (logfilecountt___bit_eq Int Int Int )
    (logfileentryt___arr_element logfileentryt Int Int )
    (logfileentryt___arr_update
      logfileentryt
      Int
      Int
      logfileentryt
    )
    (logfileentryt___bit_eq logfileentryt logfileentryt Int )
    (logfileentryt___mk_const_arr Int logfileentryt )
    (logfilelistentriest___arr_element
      logfilelistentriest
      Int
      Int
    )
    (logfilelistentriest___arr_update
      logfilelistentriest
      Int
      Int
      logfilelistentriest
    )
    (logfilelistentriest___bit_eq
      logfilelistentriest
      logfilelistentriest
      Int
    )
    (logfilelistentriest___mk_const_arr
      Int
      logfilelistentriest
    )
    (logfilelistt___bit_eq logfilelistt logfilelistt Int )
    (logfilelistt___head___rcd_element logfilelistt Int )
    (logfilelistt___head___rcd_update
      logfilelistt
      Int
      logfilelistt
    )
    (logfilelistt___lasti___rcd_element logfilelistt Int )
    (logfilelistt___lasti___rcd_update
      logfilelistt
      Int
      logfilelistt
    )
    (logfilelistt___length___rcd_element logfilelistt Int )
    (logfilelistt___length___rcd_update
      logfilelistt
      Int
      logfilelistt
    )
    (logfilelistt___list___rcd_element
      logfilelistt
      logfilelistentriest
    )
    (logfilelistt___list___rcd_update
      logfilelistt
      logfilelistentriest
      logfilelistt
    )
    (logfilesstatust___arr_element logfilesstatust Int Int )
    (logfilesstatust___arr_update
      logfilesstatust
      Int
      Int
      logfilesstatust
    )
    (logfilesstatust___bit_eq
      logfilesstatust
      logfilesstatust
      Int
    )
    (logfilesstatust___mk_const_arr Int logfilesstatust )
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
  ( (alarmtypes__statust__LE Int Int )
    (alarmtypes__statust__LT Int Int )
    (alarmtypes__statust___member Int )
    (audittypes__elementt__LE Int Int )
    (audittypes__elementt__LT Int Int )
    (audittypes__elementt___member Int )
    (audittypes__severityt__LE Int Int )
    (audittypes__severityt__LT Int Int )
    (audittypes__severityt___member Int )
    (bit___type___member Int )
    (filestatust__LE Int Int )
    (filestatust__LT Int Int )
    (filestatust___member Int )
    (int___odd Int )
    (logfilesstatust___member logfilesstatust )
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
    (implies
      (filestatust___member ?i )
      (= (filestatust__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (filestatust___member ?i )
      (= (filestatust__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (filestatust___member ?i )
      (implies (< ?i 2 ) (= (filestatust__succ ?i ) (+ ?i 1 ) ) )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (filestatust___member ?i )
      (implies (< 0 ?i ) (= (filestatust__pred ?i ) (- ?i 1 ) ) )
    )
  )
  :assumption
  (= free 0 )
  :assumption
  (= archived 1 )
  :assumption
  (= used 2 )
  :assumption
  (= maxlogfileentries 1024 )
  :assumption
  (= maxlogentries 17408 )
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
  (<= 0 audittypes__usertexti__size )
  :assumption
  (= audittypes__usertexti__first 1 )
  :assumption
  (= audittypes__usertexti__last 50 )
  :assumption
  (= audittypes__usertexti__base__first (~ 2147483648 ) )
  :assumption
  (= audittypes__usertexti__base__last 2147483647 )
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
  (<= 0 logfilecountt__size )
  :assumption
  (= logfilecountt__first 0 )
  :assumption
  (= logfilecountt__last 17 )
  :assumption
  (<= logfilecountt__base__first logfilecountt__base__last )
  :assumption
  (<= logfilecountt__base__first logfilecountt__first )
  :assumption
  (<= logfilecountt__last logfilecountt__base__last )
  :assumption
  (<= 0 logfileindext__size )
  :assumption
  (= logfileindext__first 1 )
  :assumption
  (= logfileindext__last 17 )
  :assumption
  (<= logfileindext__base__first logfileindext__base__last )
  :assumption
  (<= logfileindext__base__first logfileindext__first )
  :assumption
  (<= logfileindext__last logfileindext__base__last )
  :assumption
  (<= 0 filestatust__size )
  :assumption
  (= filestatust__first free )
  :assumption
  (= filestatust__last used )
  :assumption
  (= filestatust__base__first free )
  :assumption
  (= filestatust__base__last used )
  :assumption
  (<= 0 logentrycountt__size )
  :assumption
  (= logentrycountt__first 0 )
  :assumption
  (= logentrycountt__last 17408 )
  :assumption
  (<= logentrycountt__base__first logentrycountt__base__last )
  :assumption
  (<= logentrycountt__base__first logentrycountt__first )
  :assumption
  (<= logentrycountt__last logentrycountt__base__last )
  :assumption
  (<= 0 fileentrycountt__size )
  :assumption
  (= fileentrycountt__first 0 )
  :assumption
  (= fileentrycountt__last 1024 )
  :assumption
  (<=
    fileentrycountt__base__first
    fileentrycountt__base__last
  )
  :assumption
  (<= fileentrycountt__base__first fileentrycountt__first )
  :assumption
  (<= fileentrycountt__last fileentrycountt__base__last )
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
  (filestatust___member archived )
  :assumption
  (alarmtypes__statust___member auditalarm )
  :assumption
  (alarmtypes__statust___member auditalarm__1 )
  :assumption
  (alarmtypes__statust___member auditalarm__1___init )
  :assumption
  (alarmtypes__statust___member auditalarm__1___loopinit )
  :assumption
  (alarmtypes__statust___member auditalarm___init )
  :assumption
  (alarmtypes__statust___member auditalarm___loopinit )
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
  (audittypes__elementt___member elementid )
  :assumption
  (audittypes__elementt___member elementid___init )
  :assumption
  (audittypes__elementt___member elementid___loopinit )
  :assumption
  (filestatust___member filestatust__base__first )
  :assumption
  (filestatust___member filestatust__base__last )
  :assumption
  (filestatust___member filestatust__first )
  :assumption
  (filestatust___member filestatust__last )
  :assumption
  (filestatust___member free )
  :assumption
  (logfilesstatust___member logfilesstatus )
  :assumption
  (logfilesstatust___member logfilesstatus__1 )
  :assumption
  (logfilesstatust___member logfilesstatus__1___init )
  :assumption
  (logfilesstatust___member logfilesstatus__1___loopinit )
  :assumption
  (logfilesstatust___member logfilesstatus__2 )
  :assumption
  (logfilesstatust___member logfilesstatus__2___init )
  :assumption
  (logfilesstatust___member logfilesstatus__2___loopinit )
  :assumption
  (logfilesstatust___member logfilesstatus__3 )
  :assumption
  (logfilesstatust___member logfilesstatus__3___init )
  :assumption
  (logfilesstatust___member logfilesstatus__3___loopinit )
  :assumption
  (logfilesstatust___member logfilesstatus___init )
  :assumption
  (logfilesstatust___member logfilesstatus___loopinit )
  :assumption
  (audittypes__severityt___member severity )
  :assumption
  (audittypes__severityt___member severity___init )
  :assumption
  (audittypes__severityt___member severity___loopinit )
  :assumption
  (filestatust___member used )
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
      (filestatust___member ?x0 )
      (filestatust___member (filestatust__pred ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (filestatust___member ?x0 )
      (filestatust___member (filestatust__succ ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (filestatust___member (filestatust__val ?x0 ) )
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
      (filestatust___member ?x )
      (and (<= 0 ?x ) (<= ?x 2 ) )
    )
  )
  :assumption
  (forall
      (?x logfilesstatust )
    (iff
      (logfilesstatust___member ?x )
      (forall
          (?s0 Int )
        (and
          (filestatust___member
            (logfilesstatust___arr_element ?x ?s0 )
          )
          true
        )
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
      (?x Int ) (?y Int )
    (iff
      (= (alarmtypes__statust___bit_eq ?x ?y ) bit___true )
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
      (= (character___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (filestatust___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (logentrycountt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (logfilecountt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x logfileentryt ) (?y logfileentryt )
    (iff
      (= (logfileentryt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x logfilelistentriest ) (?y logfilelistentriest )
    (iff
      (= (logfilelistentriest___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x logfilelistt ) (?y logfilelistt )
    (iff
      (= (logfilelistt___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x logfilesstatust ) (?y logfilesstatust )
    (iff
      (= (logfilesstatust___bit_eq ?x ?y ) bit___true )
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
      (logfilesstatust___arr_element
        (logfilesstatust___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v Int )
    (=
      (logfilelistentriest___arr_element
        (logfilelistentriest___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v Int )
    (=
      (logfileentryt___arr_element
        (logfileentryt___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a logfileentryt ) (?s0 Int ) (?t Int )
    (=
      (logfileentryt___arr_element
        (logfileentryt___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a logfileentryt ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (logfileentryt___arr_element
          (logfileentryt___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (logfileentryt___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a logfilelistentriest ) (?s0 Int ) (?t Int )
    (=
      (logfilelistentriest___arr_element
        (logfilelistentriest___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a logfilelistentriest ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (logfilelistentriest___arr_element
          (logfilelistentriest___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (logfilelistentriest___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a logfilesstatust ) (?s0 Int ) (?t Int )
    (=
      (logfilesstatust___arr_element
        (logfilesstatust___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a logfilesstatust ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (logfilesstatust___arr_element
          (logfilesstatust___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (logfilesstatust___arr_element ?a ?s0p )
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
      (?r logfilelistt ) (?t logfilelistentriest )
    (=
      (logfilelistt___list___rcd_element
        (logfilelistt___list___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___list___rcd_element
        (logfilelistt___head___rcd_update ?r ?t )
      )
      (logfilelistt___list___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___list___rcd_element
        (logfilelistt___lasti___rcd_update ?r ?t )
      )
      (logfilelistt___list___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___list___rcd_element
        (logfilelistt___length___rcd_update ?r ?t )
      )
      (logfilelistt___list___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t logfilelistentriest )
    (=
      (logfilelistt___head___rcd_element
        (logfilelistt___list___rcd_update ?r ?t )
      )
      (logfilelistt___head___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___head___rcd_element
        (logfilelistt___head___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___head___rcd_element
        (logfilelistt___lasti___rcd_update ?r ?t )
      )
      (logfilelistt___head___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___head___rcd_element
        (logfilelistt___length___rcd_update ?r ?t )
      )
      (logfilelistt___head___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t logfilelistentriest )
    (=
      (logfilelistt___lasti___rcd_element
        (logfilelistt___list___rcd_update ?r ?t )
      )
      (logfilelistt___lasti___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___lasti___rcd_element
        (logfilelistt___head___rcd_update ?r ?t )
      )
      (logfilelistt___lasti___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___lasti___rcd_element
        (logfilelistt___lasti___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___lasti___rcd_element
        (logfilelistt___length___rcd_update ?r ?t )
      )
      (logfilelistt___lasti___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t logfilelistentriest )
    (=
      (logfilelistt___length___rcd_element
        (logfilelistt___list___rcd_update ?r ?t )
      )
      (logfilelistt___length___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___length___rcd_element
        (logfilelistt___head___rcd_update ?r ?t )
      )
      (logfilelistt___length___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___length___rcd_element
        (logfilelistt___lasti___rcd_update ?r ?t )
      )
      (logfilelistt___length___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r logfilelistt ) (?t Int )
    (=
      (logfilelistt___length___rcd_element
        (logfilelistt___length___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :formula
  (and
    (<= audittypes__startunenrolledtis elementid )
    (<= elementid audittypes__systemfault )
    (<= audittypes__information severity )
    (<= severity audittypes__critical )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 50 ) )
        (and
          (<= 0 (string___arr_element user ?i___1 ) )
          (<= (string___arr_element user ?i___1 ) 255 )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 150 ) )
        (and
          (<= 0 (string___arr_element description ?i___1 ) )
          (<= (string___arr_element description ?i___1 ) 255 )
        )
      )
    )
    (<= alarmtypes__alarming auditalarm )
    (<= auditalarm alarmtypes__silent )
    (<=
      0
      (+
        (*
          (- (logfilelistt___length___rcd_element usedlogfiles ) 1 )
          1024
        )
        (logfileentryt___arr_element logfileentries currentlogfile )
      )
    )
    (<=
      (+
        (*
          (- (logfilelistt___length___rcd_element usedlogfiles ) 1 )
          1024
        )
        (logfileentryt___arr_element logfileentries currentlogfile )
      )
      17408
    )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 17 ) )
        (and
          (<=
            free
            (logfilesstatust___arr_element logfilesstatus ?i___1 )
          )
          (<=
            (logfilesstatust___arr_element logfilesstatus ?i___1 )
            used
          )
        )
      )
    )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 17 ) )
        (and
          (<= 0 (logfileentryt___arr_element logfileentries ?i___1 ) )
          (<=
            (logfileentryt___arr_element logfileentries ?i___1 )
            1024
          )
        )
      )
    )
    (<= 1 currentlogfile )
    (<= currentlogfile 17 )
    (<= 0 (logfilelistt___length___rcd_element usedlogfiles ) )
    (<= (logfilelistt___length___rcd_element usedlogfiles ) 17 )
    (<= 1 (logfilelistt___lasti___rcd_element usedlogfiles ) )
    (<= (logfilelistt___lasti___rcd_element usedlogfiles ) 17 )
    (<= 1 (logfilelistt___head___rcd_element usedlogfiles ) )
    (<= (logfilelistt___head___rcd_element usedlogfiles ) 17 )
    (forall
        (?i___1 Int )
      (implies
        (and (<= 1 ?i___1 ) (<= ?i___1 17 ) )
        (and
          (<=
            1
            (logfilelistentriest___arr_element
              (logfilelistt___list___rcd_element usedlogfiles )
              ?i___1
            )
          )
          (<=
            (logfilelistentriest___arr_element
              (logfilelistt___list___rcd_element usedlogfiles )
              ?i___1
            )
            17
          )
        )
      )
    )
    (or
      (not
        (=
          (logfileentryt___arr_element logfileentries currentlogfile )
          1024
        )
      )
      (not
        (= (logfilelistt___length___rcd_element usedlogfiles ) 17 )
      )
    )
    (<= 0 integer__size )
    (<= 0 character__size )
    (<= 0 positive__size )
    (<= 0 audittypes__elementt__size )
    (<= 0 audittypes__severityt__size )
    (<= 0 audittypes__descriptioni__size )
    (<= 0 audittypes__usertexti__size )
    (<= 0 alarmtypes__statust__size )
    (<= 0 logfilecountt__size )
    (<= logfilecountt__base__first logfilecountt__base__last )
    (<= 0 logfileindext__size )
    (<= logfileindext__base__first logfileindext__base__last )
    (<= 0 filestatust__size )
    (<= 0 logentrycountt__size )
    (<= logentrycountt__base__first logentrycountt__base__last )
    (<= 0 fileentrycountt__size )
    (<=
      fileentrycountt__base__first
      fileentrycountt__base__last
    )
    (<= logfilecountt__base__first 0 )
    (<= 17 logfilecountt__base__last )
    (<= logfileindext__base__first 1 )
    (<= 17 logfileindext__base__last )
    (<= logentrycountt__base__first 0 )
    (<= 17408 logentrycountt__base__last )
    (<= fileentrycountt__base__first 0 )
    (<= 1024 fileentrycountt__base__last )
    (not
      (or
        (<
          (logfileentryt___arr_element logfileentries currentlogfile )
          1024
        )
        (< (logfilelistt___length___rcd_element usedlogfiles ) 17 )
      )
    )
  )
  :status unknown
)
