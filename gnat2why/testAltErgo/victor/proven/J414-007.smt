(benchmark file_string_contains_short_string.1.1
  :logic AUFNIRA
  :extrasorts ( string real___type )
  :extrafuns 
  ( (base_file_string_index__base__first Int )
    (base_file_string_index__base__last Int )
    (base_file_string_index__first Int )
    (base_file_string_index__last Int )
    (base_file_string_index__size Int )
    (bit___false Int )
    (bit___true Int )
    (character__base__first Int )
    (character__base__last Int )
    (character__first Int )
    (character__last Int )
    (character__size Int )
    (file_string_index__base__first Int )
    (file_string_index__base__last Int )
    (file_string_index__first Int )
    (file_string_index__last Int )
    (file_string_index__size Int )
    (inc_item string )
    (inc_item___init string )
    (inc_item___loopinit string )
    (inc_item_last Int )
    (inc_item_last___init Int )
    (inc_item_last___loopinit Int )
    (inc_item_last__entry__loop__1 Int )
    (inc_item_last__entry__loop__1___init Int )
    (inc_item_last__entry__loop__1___loopinit Int )
    (integer__base__first Int )
    (integer__base__last Int )
    (integer__first Int )
    (integer__last Int )
    (integer__size Int )
    (loop__1__i Int )
    (loop__1__i___init Int )
    (loop__1__i___loopinit Int )
    (null__string string )
    (positive__base__first Int )
    (positive__base__last Int )
    (positive__first Int )
    (positive__last Int )
    (positive__size Int )
    (short_string_index__base__first Int )
    (short_string_index__base__last Int )
    (short_string_index__first Int )
    (short_string_index__last Int )
    (short_string_index__size Int )
    (source string )
    (source___init string )
    (source___loopinit string )
    (source_index Int )
    (source_index___init Int )
    (source_index___loopinit Int )
    (string___default_arr string )
    (string___default_arr_element Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (character___bit_eq Int Int Int )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (real___bit_eq real___type real___type Int )
    (round__ real___type Int )
    (string___arr_element string Int Int )
    (string___arr_update string Int Int string )
    (string___bit_eq string string Int )
    (string___mk_const_arr Int string )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (<= 0 integer__size )
  :assumption
  (<= integer__first integer__last )
  :assumption
  (<= integer__base__first integer__base__last )
  :assumption
  (<= integer__base__first integer__first )
  :assumption
  (<= integer__last integer__base__last )
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
  (<= positive__first positive__last )
  :assumption
  (<= positive__base__first positive__base__last )
  :assumption
  (<= positive__base__first positive__first )
  :assumption
  (<= positive__last positive__base__last )
  :assumption
  (<= 0 base_file_string_index__size )
  :assumption
  (= base_file_string_index__first 0 )
  :assumption
  (= base_file_string_index__last 100000 )
  :assumption
  (<=
    base_file_string_index__base__first
    base_file_string_index__base__last
  )
  :assumption
  (<=
    base_file_string_index__base__first
    base_file_string_index__first
  )
  :assumption
  (<=
    base_file_string_index__last
    base_file_string_index__base__last
  )
  :assumption
  (<= 0 file_string_index__size )
  :assumption
  (= file_string_index__first 1 )
  :assumption
  (= file_string_index__last 100000 )
  :assumption
  (<=
    file_string_index__base__first
    file_string_index__base__last
  )
  :assumption
  (<=
    file_string_index__base__first
    file_string_index__first
  )
  :assumption
  (<= file_string_index__last file_string_index__base__last )
  :assumption
  (<= 0 short_string_index__size )
  :assumption
  (= short_string_index__first 1 )
  :assumption
  (= short_string_index__last 100 )
  :assumption
  (<=
    short_string_index__base__first
    short_string_index__base__last
  )
  :assumption
  (<=
    short_string_index__base__first
    short_string_index__first
  )
  :assumption
  (<=
    short_string_index__last
    short_string_index__base__last
  )
  :assumption
  (<= 0 integer__size )
  :assumption
  (<= integer__first integer__last )
  :assumption
  (<= integer__base__first integer__base__last )
  :assumption
  (<= integer__base__first integer__first )
  :assumption
  (<= integer__last integer__base__last )
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
  (<= positive__first positive__last )
  :assumption
  (<= positive__base__first positive__base__last )
  :assumption
  (<= positive__base__first positive__first )
  :assumption
  (<= positive__last positive__base__last )
  :assumption
  (<= 0 base_file_string_index__size )
  :assumption
  (= base_file_string_index__first 0 )
  :assumption
  (= base_file_string_index__last 100000 )
  :assumption
  (<=
    base_file_string_index__base__first
    base_file_string_index__base__last
  )
  :assumption
  (<=
    base_file_string_index__base__first
    base_file_string_index__first
  )
  :assumption
  (<=
    base_file_string_index__last
    base_file_string_index__base__last
  )
  :assumption
  (<= 0 file_string_index__size )
  :assumption
  (= file_string_index__first 1 )
  :assumption
  (= file_string_index__last 100000 )
  :assumption
  (<=
    file_string_index__base__first
    file_string_index__base__last
  )
  :assumption
  (<=
    file_string_index__base__first
    file_string_index__first
  )
  :assumption
  (<= file_string_index__last file_string_index__base__last )
  :assumption
  (<= 0 short_string_index__size )
  :assumption
  (= short_string_index__first 1 )
  :assumption
  (= short_string_index__last 100 )
  :assumption
  (<=
    short_string_index__base__first
    short_string_index__base__last
  )
  :assumption
  (<=
    short_string_index__base__first
    short_string_index__first
  )
  :assumption
  (<=
    short_string_index__last
    short_string_index__base__last
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
    (iff
      (= (character___bit_eq ?x ?y ) bit___true )
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
  (< 0 source_index )
  :assumption
  (<= (+ source_index inc_item_last ) 100001 )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and (<= 1 ?i___1 ) (<= ?i___1 100000 ) )
      (and
        (<= 0 (string___arr_element source ?i___1 ) )
        (<= (string___arr_element source ?i___1 ) 255 )
      )
    )
  )
  :assumption
  (<= source_index 100000 )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and (<= 1 ?i___1 ) (<= ?i___1 100000 ) )
      (and
        (<= 0 (string___arr_element inc_item ?i___1 ) )
        (<= (string___arr_element inc_item ?i___1 ) 255 )
      )
    )
  )
  :assumption
  (<= 1 inc_item_last )
  :assumption
  (<= inc_item_last 100000 )
  :assumption
  (=
    (string___arr_element source source_index )
    (string___arr_element inc_item 1 )
  )
  :assumption
  (<= 0 integer__size )
  :assumption
  (<= 0 character__size )
  :assumption
  (<= 0 positive__size )
  :assumption
  (<= 0 base_file_string_index__size )
  :assumption
  (<= 0 file_string_index__size )
  :assumption
  (<= 0 short_string_index__size )
  :formula
  (not
    (forall
        (?x_ Int )
      (implies
        (and (<= 1 ?x_ ) (<= ?x_ 1 ) )
        (=
          (string___arr_element source (- (+ ?x_ source_index ) 1 ) )
          (string___arr_element inc_item ?x_ )
        )
      )
    )
  )
  :status unknown
)
