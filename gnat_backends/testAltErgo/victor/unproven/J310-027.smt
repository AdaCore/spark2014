(benchmark selection.6.1
  :logic AUFNIRA
  :extrasorts ( location_property real___type )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (current Int )
    (current___init Int )
    (current___loopinit Int )
    (du_available location_property )
    (du_available___init location_property )
    (du_available___loopinit location_property )
    (extended_location__base__first Int )
    (extended_location__base__last Int )
    (extended_location__first Int )
    (extended_location__last Int )
    (extended_location__size Int )
    (left Int )
    (location__base__first Int )
    (location__base__last Int )
    (location__first Int )
    (location__last Int )
    (location__size Int )
    (location_property___default_arr location_property )
    (location_property___default_arr_element Int )
    (nil Int )
    (request location_property )
    (request___init location_property )
    (request___loopinit location_property )
    (right Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (change_side Int Int )
    (extended_location___bit_eq Int Int Int )
    (extended_location__pos Int Int )
    (extended_location__pred Int Int )
    (extended_location__succ Int Int )
    (extended_location__val Int Int )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (location_property___arr_element location_property Int Int )
    (location_property___arr_update
      location_property
      Int
      Int
      location_property
    )
    (location_property___bit_eq
      location_property
      location_property
      Int
    )
    (location_property___mk_const_arr Int location_property )
    (real___bit_eq real___type real___type Int )
    (round__ real___type Int )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (extended_location__LE Int Int )
    (extended_location__LT Int Int )
    (extended_location___member Int )
    (fulfill_condition Int location_property location_property )
    (location_property___member location_property )
    (none_available location_property )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (extended_location___member ?i )
      (= (extended_location__pos ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (extended_location___member ?i )
      (= (extended_location__val ?i ) ?i )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (extended_location___member ?i )
      (implies
        (< ?i 2 )
        (= (extended_location__succ ?i ) (+ ?i 1 ) )
      )
    )
  )
  :assumption
  (forall
      (?i Int )
    (implies
      (extended_location___member ?i )
      (implies
        (< 0 ?i )
        (= (extended_location__pred ?i ) (- ?i 1 ) )
      )
    )
  )
  :assumption
  (= nil 0 )
  :assumption
  (= left 1 )
  :assumption
  (= right 2 )
  :assumption
  (<= 0 extended_location__size )
  :assumption
  (= extended_location__first nil )
  :assumption
  (= extended_location__last right )
  :assumption
  (= extended_location__base__first nil )
  :assumption
  (= extended_location__base__last right )
  :assumption
  (<= 0 location__size )
  :assumption
  (= location__first left )
  :assumption
  (= location__last right )
  :assumption
  (= location__base__first nil )
  :assumption
  (= location__base__last right )
  :assumption
  (<= 0 extended_location__size )
  :assumption
  (= extended_location__first nil )
  :assumption
  (= extended_location__last right )
  :assumption
  (= extended_location__base__first nil )
  :assumption
  (= extended_location__base__last right )
  :assumption
  (<= 0 location__size )
  :assumption
  (= location__first left )
  :assumption
  (= location__last right )
  :assumption
  (= location__base__first nil )
  :assumption
  (= location__base__last right )
  :assumption
  (extended_location___member current )
  :assumption
  (extended_location___member current___init )
  :assumption
  (extended_location___member current___loopinit )
  :assumption
  (location_property___member du_available )
  :assumption
  (location_property___member du_available___init )
  :assumption
  (location_property___member du_available___loopinit )
  :assumption
  (extended_location___member extended_location__base__first )
  :assumption
  (extended_location___member extended_location__base__last )
  :assumption
  (extended_location___member extended_location__first )
  :assumption
  (extended_location___member extended_location__last )
  :assumption
  (extended_location___member left )
  :assumption
  (extended_location___member location__base__first )
  :assumption
  (extended_location___member location__base__last )
  :assumption
  (extended_location___member location__first )
  :assumption
  (extended_location___member location__last )
  :assumption
  (extended_location___member nil )
  :assumption
  (location_property___member request )
  :assumption
  (location_property___member request___init )
  :assumption
  (location_property___member request___loopinit )
  :assumption
  (extended_location___member right )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (extended_location___member ?x0 )
      (extended_location___member (change_side ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (extended_location___member ?x0 )
      (extended_location___member (extended_location__pred ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (implies
      (extended_location___member ?x0 )
      (extended_location___member (extended_location__succ ?x0 ) )
    )
  )
  :assumption
  (forall
      (?x0 Int )
    (extended_location___member (extended_location__val ?x0 ) )
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
      (extended_location___member ?x )
      (and (<= 0 ?x ) (<= ?x 2 ) )
    )
  )
  :assumption
  (forall
      (?x location_property )
    (iff
      (location_property___member ?x )
      (forall
          (?s0 Int )
        (and
          (implies
            (extended_location___member ?s0 )
            (bit___type___member
              (location_property___arr_element ?x ?s0 )
            )
          )
          (implies
            (not (extended_location___member ?s0 ) )
            (=
              (location_property___arr_element ?x ?s0 )
              location_property___default_arr_element
            )
          )
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
      (= (extended_location___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x location_property ) (?y location_property )
    (iff
      (= (location_property___bit_eq ?x ?y ) bit___true )
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
      (location_property___arr_element
        (location_property___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a location_property ) (?s0 Int ) (?t Int )
    (=
      (location_property___arr_element
        (location_property___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a location_property ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (location_property___arr_element
          (location_property___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (location_property___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  true
  :assumption
  (<= extended_location__first current )
  :assumption
  (<= current extended_location__last )
  :assumption
  true
  :assumption
  true
  :assumption
  (<= location__first left )
  :assumption
  (<= left location__last )
  :assumption
  true
  :assumption
  (iff
    (fulfill_condition left request du_available )
    (and
      (=
        (location_property___arr_element du_available left )
        bit___true
      )
      (or
        (=
          (location_property___arr_element request left )
          bit___true
        )
        (not
          (=
            (location_property___arr_element
              du_available
              (change_side left )
            )
            bit___true
          )
        )
      )
    )
  )
  :assumption
  (not (fulfill_condition left request du_available ) )
  :assumption
  (<= location__first right )
  :assumption
  (<= right location__last )
  :assumption
  true
  :assumption
  (iff
    (fulfill_condition right request du_available )
    (and
      (=
        (location_property___arr_element du_available right )
        bit___true
      )
      (or
        (=
          (location_property___arr_element request right )
          bit___true
        )
        (not
          (=
            (location_property___arr_element
              du_available
              (change_side right )
            )
            bit___true
          )
        )
      )
    )
  )
  :assumption
  (not (fulfill_condition right request du_available ) )
  :assumption
  true
  :assumption
  (iff
    (none_available du_available )
    (and
      (not
        (=
          (location_property___arr_element du_available left )
          bit___true
        )
      )
      (not
        (=
          (location_property___arr_element du_available right )
          bit___true
        )
      )
    )
  )
  :assumption
  (not (none_available du_available ) )
  :formula
  (not
    (and
      (=
        (location_property___arr_element du_available left )
        bit___true
      )
      (=
        (location_property___arr_element du_available right )
        bit___true
      )
    )
  )
  :status unknown
)
