(benchmark disconnect_node.14.1
  :logic AUFNIRA
  :extrasorts 
  ( item
    node_index_array
    user_index_array
    node
    ob_stack
    nodes_arr
    ob_tree
    real___type
  )
  :extrafuns 
  ( (bit___false Int )
    (bit___true Int )
    (index_t__base__first Int )
    (index_t__base__last Int )
    (index_t__first Int )
    (index_t__last Int )
    (index_t__size Int )
    (item___default_rcd item )
    (item__size Int )
    (key_t__base__first Int )
    (key_t__base__last Int )
    (key_t__first Int )
    (key_t__last Int )
    (key_t__size Int )
    (node___default_rcd node )
    (node__size Int )
    (node_index_array___default_arr node_index_array )
    (node_index_array___default_arr_element Int )
    (node_index_t__base__first Int )
    (node_index_t__base__last Int )
    (node_index_t__first Int )
    (node_index_t__last Int )
    (node_index_t__size Int )
    (nodes_arr___default_arr nodes_arr )
    (nodes_arr___default_arr_element node )
    (null_node_index Int )
    (ob_stack___default_rcd ob_stack )
    (ob_stack__size Int )
    (ob_tree___default_rcd ob_tree )
    (ob_tree__size Int )
    (previous Int )
    (previous___init Int )
    (previous___loopinit Int )
    (tree ob_tree )
    (tree___init ob_tree )
    (tree___loopinit ob_tree )
    (user_index_array___default_arr user_index_array )
    (user_index_array___default_arr_element Int )
    (user_index_t__base__first Int )
    (user_index_t__base__last Int )
    (user_index_t__first Int )
    (user_index_t__last Int )
    (user_index_t__size Int )
    (x_node Int )
    (x_node___init Int )
    (x_node___loopinit Int )
    (bit___and Int Int Int )
    (bit___iff Int Int Int )
    (bit___not Int Int )
    (bit___or Int Int Int )
    (bit___type___bit_eq Int Int Int )
    (index_t___bit_eq Int Int Int )
    (integer___bit_eq Int Int Int )
    (integer___bit_le Int Int Int )
    (item___bit_eq item item Int )
    (item___index___rcd_element item Int )
    (item___index___rcd_update item Int item )
    (item___key___rcd_element item Int )
    (item___key___rcd_update item Int item )
    (key_t___bit_eq Int Int Int )
    (node___bit_eq node node Int )
    (node___data___rcd_element node item )
    (node___data___rcd_update node item node )
    (node___left___rcd_element node Int )
    (node___left___rcd_update node Int node )
    (node___right___rcd_element node Int )
    (node___right___rcd_update node Int node )
    (node_index_array___arr_element node_index_array Int Int )
    (node_index_array___arr_update
      node_index_array
      Int
      Int
      node_index_array
    )
    (node_index_array___bit_eq
      node_index_array
      node_index_array
      Int
    )
    (node_index_array___mk_const_arr Int node_index_array )
    (node_index_t___bit_eq Int Int Int )
    (nodes_arr___arr_element nodes_arr Int node )
    (nodes_arr___arr_update nodes_arr Int node nodes_arr )
    (nodes_arr___bit_eq nodes_arr nodes_arr Int )
    (nodes_arr___mk_const_arr node nodes_arr )
    (ob_stack___bit_eq ob_stack ob_stack Int )
    (ob_stack___data_stack___rcd_element
      ob_stack
      user_index_array
    )
    (ob_stack___data_stack___rcd_update
      ob_stack
      user_index_array
      ob_stack
    )
    (ob_stack___node_stack___rcd_element
      ob_stack
      node_index_array
    )
    (ob_stack___node_stack___rcd_update
      ob_stack
      node_index_array
      ob_stack
    )
    (ob_stack___top___rcd_element ob_stack Int )
    (ob_stack___top___rcd_update ob_stack Int ob_stack )
    (ob_tree___bit_eq ob_tree ob_tree Int )
    (ob_tree___free___rcd_element ob_tree ob_stack )
    (ob_tree___free___rcd_update ob_tree ob_stack ob_tree )
    (ob_tree___nodes___rcd_element ob_tree nodes_arr )
    (ob_tree___nodes___rcd_update ob_tree nodes_arr ob_tree )
    (real___bit_eq real___type real___type Int )
    (round__ real___type Int )
    (size_of ob_tree Int Int )
    (user_index_array___arr_element user_index_array Int Int )
    (user_index_array___arr_update
      user_index_array
      Int
      Int
      user_index_array
    )
    (user_index_array___bit_eq
      user_index_array
      user_index_array
      Int
    )
    (user_index_array___mk_const_arr Int user_index_array )
  )
  :extrapreds 
  ( (bit___type___member Int )
    (real___le real___type real___type )
    (real___lt real___type real___type )
  )
  :assumption
  (= null_node_index 0 )
  :assumption
  (<= 0 index_t__size )
  :assumption
  (= index_t__first 0 )
  :assumption
  (= index_t__last 1000 )
  :assumption
  (<= index_t__base__first index_t__base__last )
  :assumption
  (<= index_t__base__first index_t__first )
  :assumption
  (<= index_t__last index_t__base__last )
  :assumption
  (<= 0 key_t__size )
  :assumption
  (= key_t__first (~ 2147483648 ) )
  :assumption
  (= key_t__last 2147483647 )
  :assumption
  (<= key_t__base__first key_t__base__last )
  :assumption
  (<= key_t__base__first key_t__first )
  :assumption
  (<= key_t__last key_t__base__last )
  :assumption
  (<= 0 node_index_t__size )
  :assumption
  (= node_index_t__first 0 )
  :assumption
  (= node_index_t__last 1000 )
  :assumption
  (<= node_index_t__base__first node_index_t__base__last )
  :assumption
  (<= node_index_t__base__first node_index_t__first )
  :assumption
  (<= node_index_t__last node_index_t__base__last )
  :assumption
  (<= 0 user_index_t__size )
  :assumption
  (= user_index_t__first 0 )
  :assumption
  (= user_index_t__last 1000 )
  :assumption
  (<= user_index_t__base__first user_index_t__base__last )
  :assumption
  (<= user_index_t__base__first user_index_t__first )
  :assumption
  (<= user_index_t__last user_index_t__base__last )
  :assumption
  (= null_node_index 0 )
  :assumption
  (<= 0 index_t__size )
  :assumption
  (= index_t__first 0 )
  :assumption
  (= index_t__last 1000 )
  :assumption
  (<= index_t__base__first index_t__base__last )
  :assumption
  (<= index_t__base__first index_t__first )
  :assumption
  (<= index_t__last index_t__base__last )
  :assumption
  (<= 0 key_t__size )
  :assumption
  (= key_t__first (~ 2147483648 ) )
  :assumption
  (= key_t__last 2147483647 )
  :assumption
  (<= key_t__base__first key_t__base__last )
  :assumption
  (<= key_t__base__first key_t__first )
  :assumption
  (<= key_t__last key_t__base__last )
  :assumption
  (<= 0 node_index_t__size )
  :assumption
  (= node_index_t__first 0 )
  :assumption
  (= node_index_t__last 1000 )
  :assumption
  (<= node_index_t__base__first node_index_t__base__last )
  :assumption
  (<= node_index_t__base__first node_index_t__first )
  :assumption
  (<= node_index_t__last node_index_t__base__last )
  :assumption
  (<= 0 user_index_t__size )
  :assumption
  (= user_index_t__first 0 )
  :assumption
  (= user_index_t__last 1000 )
  :assumption
  (<= user_index_t__base__first user_index_t__base__last )
  :assumption
  (<= user_index_t__base__first user_index_t__first )
  :assumption
  (<= user_index_t__last user_index_t__base__last )
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
    (iff (= (index_t___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x item ) (?y item )
    (iff (= (item___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff (= (key_t___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x node ) (?y node )
    (iff (= (node___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x node_index_array ) (?y node_index_array )
    (iff
      (= (node_index_array___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x Int ) (?y Int )
    (iff
      (= (node_index_t___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x nodes_arr ) (?y nodes_arr )
    (iff
      (= (nodes_arr___bit_eq ?x ?y ) bit___true )
      (= ?x ?y )
    )
  )
  :assumption
  (forall
      (?x ob_stack ) (?y ob_stack )
    (iff (= (ob_stack___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x ob_tree ) (?y ob_tree )
    (iff (= (ob_tree___bit_eq ?x ?y ) bit___true ) (= ?x ?y ) )
  )
  :assumption
  (forall
      (?x user_index_array ) (?y user_index_array )
    (iff
      (= (user_index_array___bit_eq ?x ?y ) bit___true )
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
      (node_index_array___arr_element
        (node_index_array___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v Int )
    (=
      (user_index_array___arr_element
        (user_index_array___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?i1 Int ) (?v node )
    (=
      (nodes_arr___arr_element
        (nodes_arr___mk_const_arr ?v )
        ?i1
      )
      ?v
    )
  )
  :assumption
  (forall
      (?a node_index_array ) (?s0 Int ) (?t Int )
    (=
      (node_index_array___arr_element
        (node_index_array___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a node_index_array ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (node_index_array___arr_element
          (node_index_array___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (node_index_array___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a nodes_arr ) (?s0 Int ) (?t node )
    (=
      (nodes_arr___arr_element
        (nodes_arr___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a nodes_arr ) (?s0 Int ) (?s0p Int ) (?t node )
    (or
      (= ?s0 ?s0p )
      (=
        (nodes_arr___arr_element
          (nodes_arr___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (nodes_arr___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?a user_index_array ) (?s0 Int ) (?t Int )
    (=
      (user_index_array___arr_element
        (user_index_array___arr_update ?a ?s0 ?t )
        ?s0
      )
      ?t
    )
  )
  :assumption
  (forall
      (?a user_index_array ) (?s0 Int ) (?s0p Int ) (?t Int )
    (or
      (= ?s0 ?s0p )
      (=
        (user_index_array___arr_element
          (user_index_array___arr_update ?a ?s0 ?t )
          ?s0p
        )
        (user_index_array___arr_element ?a ?s0p )
      )
    )
  )
  :assumption
  (forall
      (?r item ) (?t Int )
    (=
      (item___key___rcd_element (item___key___rcd_update ?r ?t ) )
      ?t
    )
  )
  :assumption
  (forall
      (?r item ) (?t Int )
    (=
      (item___key___rcd_element
        (item___index___rcd_update ?r ?t )
      )
      (item___key___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r item ) (?t Int )
    (=
      (item___index___rcd_element
        (item___key___rcd_update ?r ?t )
      )
      (item___index___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r item ) (?t Int )
    (=
      (item___index___rcd_element
        (item___index___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r node ) (?t item )
    (=
      (node___data___rcd_element
        (node___data___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r node ) (?t Int )
    (=
      (node___data___rcd_element
        (node___left___rcd_update ?r ?t )
      )
      (node___data___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r node ) (?t Int )
    (=
      (node___data___rcd_element
        (node___right___rcd_update ?r ?t )
      )
      (node___data___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r node ) (?t item )
    (=
      (node___left___rcd_element
        (node___data___rcd_update ?r ?t )
      )
      (node___left___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r node ) (?t Int )
    (=
      (node___left___rcd_element
        (node___left___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r node ) (?t Int )
    (=
      (node___left___rcd_element
        (node___right___rcd_update ?r ?t )
      )
      (node___left___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r node ) (?t item )
    (=
      (node___right___rcd_element
        (node___data___rcd_update ?r ?t )
      )
      (node___right___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r node ) (?t Int )
    (=
      (node___right___rcd_element
        (node___left___rcd_update ?r ?t )
      )
      (node___right___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r node ) (?t Int )
    (=
      (node___right___rcd_element
        (node___right___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t node_index_array )
    (=
      (ob_stack___node_stack___rcd_element
        (ob_stack___node_stack___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t user_index_array )
    (=
      (ob_stack___node_stack___rcd_element
        (ob_stack___data_stack___rcd_update ?r ?t )
      )
      (ob_stack___node_stack___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t Int )
    (=
      (ob_stack___node_stack___rcd_element
        (ob_stack___top___rcd_update ?r ?t )
      )
      (ob_stack___node_stack___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t node_index_array )
    (=
      (ob_stack___data_stack___rcd_element
        (ob_stack___node_stack___rcd_update ?r ?t )
      )
      (ob_stack___data_stack___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t user_index_array )
    (=
      (ob_stack___data_stack___rcd_element
        (ob_stack___data_stack___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t Int )
    (=
      (ob_stack___data_stack___rcd_element
        (ob_stack___top___rcd_update ?r ?t )
      )
      (ob_stack___data_stack___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t node_index_array )
    (=
      (ob_stack___top___rcd_element
        (ob_stack___node_stack___rcd_update ?r ?t )
      )
      (ob_stack___top___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t user_index_array )
    (=
      (ob_stack___top___rcd_element
        (ob_stack___data_stack___rcd_update ?r ?t )
      )
      (ob_stack___top___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_stack ) (?t Int )
    (=
      (ob_stack___top___rcd_element
        (ob_stack___top___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r ob_tree ) (?t nodes_arr )
    (=
      (ob_tree___nodes___rcd_element
        (ob_tree___nodes___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (forall
      (?r ob_tree ) (?t ob_stack )
    (=
      (ob_tree___nodes___rcd_element
        (ob_tree___free___rcd_update ?r ?t )
      )
      (ob_tree___nodes___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_tree ) (?t nodes_arr )
    (=
      (ob_tree___free___rcd_element
        (ob_tree___nodes___rcd_update ?r ?t )
      )
      (ob_tree___free___rcd_element ?r )
    )
  )
  :assumption
  (forall
      (?r ob_tree ) (?t ob_stack )
    (=
      (ob_tree___free___rcd_element
        (ob_tree___free___rcd_update ?r ?t )
      )
      ?t
    )
  )
  :assumption
  (or
    (=
      (node___left___rcd_element
        (nodes_arr___arr_element
          (ob_tree___nodes___rcd_element tree )
          previous
        )
      )
      x_node
    )
    (=
      (node___right___rcd_element
        (nodes_arr___arr_element
          (ob_tree___nodes___rcd_element tree )
          previous
        )
      )
      x_node
    )
  )
  :assumption
  (or
    (=
      (node___left___rcd_element
        (nodes_arr___arr_element
          (ob_tree___nodes___rcd_element tree )
          x_node
        )
      )
      null_node_index
    )
    (=
      (node___right___rcd_element
        (nodes_arr___arr_element
          (ob_tree___nodes___rcd_element tree )
          x_node
        )
      )
      null_node_index
    )
  )
  :assumption
  (<=
    node_index_t__first
    (ob_stack___top___rcd_element
      (ob_tree___free___rcd_element tree )
    )
  )
  :assumption
  (<=
    (ob_stack___top___rcd_element
      (ob_tree___free___rcd_element tree )
    )
    node_index_t__last
  )
  :assumption
  (forall
      (?i___3 Int )
    (implies
      (and
        (<= node_index_t__first ?i___3 )
        (<= ?i___3 node_index_t__last )
      )
      (and
        (<=
          user_index_t__first
          (user_index_array___arr_element
            (ob_stack___data_stack___rcd_element
              (ob_tree___free___rcd_element tree )
            )
            ?i___3
          )
        )
        (<=
          (user_index_array___arr_element
            (ob_stack___data_stack___rcd_element
              (ob_tree___free___rcd_element tree )
            )
            ?i___3
          )
          user_index_t__last
        )
      )
    )
  )
  :assumption
  (forall
      (?i___2 Int )
    (implies
      (and
        (<= node_index_t__first ?i___2 )
        (<= ?i___2 node_index_t__last )
      )
      (and
        (<=
          node_index_t__first
          (node_index_array___arr_element
            (ob_stack___node_stack___rcd_element
              (ob_tree___free___rcd_element tree )
            )
            ?i___2
          )
        )
        (<=
          (node_index_array___arr_element
            (ob_stack___node_stack___rcd_element
              (ob_tree___free___rcd_element tree )
            )
            ?i___2
          )
          node_index_t__last
        )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= node_index_t__first ?i___1 )
        (<= ?i___1 node_index_t__last )
      )
      (and
        (<=
          node_index_t__first
          (node___right___rcd_element
            (nodes_arr___arr_element
              (ob_tree___nodes___rcd_element tree )
              ?i___1
            )
          )
        )
        (<=
          (node___right___rcd_element
            (nodes_arr___arr_element
              (ob_tree___nodes___rcd_element tree )
              ?i___1
            )
          )
          node_index_t__last
        )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= node_index_t__first ?i___1 )
        (<= ?i___1 node_index_t__last )
      )
      (and
        (<=
          node_index_t__first
          (node___left___rcd_element
            (nodes_arr___arr_element
              (ob_tree___nodes___rcd_element tree )
              ?i___1
            )
          )
        )
        (<=
          (node___left___rcd_element
            (nodes_arr___arr_element
              (ob_tree___nodes___rcd_element tree )
              ?i___1
            )
          )
          node_index_t__last
        )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= node_index_t__first ?i___1 )
        (<= ?i___1 node_index_t__last )
      )
      (and
        (<=
          user_index_t__first
          (item___index___rcd_element
            (node___data___rcd_element
              (nodes_arr___arr_element
                (ob_tree___nodes___rcd_element tree )
                ?i___1
              )
            )
          )
        )
        (<=
          (item___index___rcd_element
            (node___data___rcd_element
              (nodes_arr___arr_element
                (ob_tree___nodes___rcd_element tree )
                ?i___1
              )
            )
          )
          user_index_t__last
        )
      )
    )
  )
  :assumption
  (forall
      (?i___1 Int )
    (implies
      (and
        (<= node_index_t__first ?i___1 )
        (<= ?i___1 node_index_t__last )
      )
      (and
        (<=
          key_t__first
          (item___key___rcd_element
            (node___data___rcd_element
              (nodes_arr___arr_element
                (ob_tree___nodes___rcd_element tree )
                ?i___1
              )
            )
          )
        )
        (<=
          (item___key___rcd_element
            (node___data___rcd_element
              (nodes_arr___arr_element
                (ob_tree___nodes___rcd_element tree )
                ?i___1
              )
            )
          )
          key_t__last
        )
      )
    )
  )
  :assumption
  (<= node_index_t__first previous )
  :assumption
  (<= previous node_index_t__last )
  :assumption
  (<= node_index_t__first x_node )
  :assumption
  (<= x_node node_index_t__last )
  :assumption
  (<= node_index_t__first previous )
  :assumption
  (<= previous node_index_t__last )
  :assumption
  (not
    (=
      (node___left___rcd_element
        (nodes_arr___arr_element
          (ob_tree___nodes___rcd_element tree )
          previous
        )
      )
      x_node
    )
  )
  :assumption
  (<= node_index_t__first x_node )
  :assumption
  (<= x_node node_index_t__last )
  :assumption
  (not
    (=
      (node___left___rcd_element
        (nodes_arr___arr_element
          (ob_tree___nodes___rcd_element tree )
          x_node
        )
      )
      null_node_index
    )
  )
  :assumption
  (=
    (size_of tree x_node )
    (+
      (size_of
        tree
        (node___left___rcd_element
          (nodes_arr___arr_element
            (ob_tree___nodes___rcd_element tree )
            x_node
          )
        )
      )
      1
    )
  )
  :assumption
  (<=
    node_index_t__first
    (node___left___rcd_element
      (nodes_arr___arr_element
        (ob_tree___nodes___rcd_element tree )
        x_node
      )
    )
  )
  :assumption
  (<=
    (node___left___rcd_element
      (nodes_arr___arr_element
        (ob_tree___nodes___rcd_element tree )
        x_node
      )
    )
    node_index_t__last
  )
  :assumption
  (<= node_index_t__first x_node )
  :assumption
  (<= x_node node_index_t__last )
  :assumption
  (<= node_index_t__first previous )
  :assumption
  (<= previous node_index_t__last )
  :formula
  (not
    (=
      (size_of
        (ob_tree___nodes___rcd_update
          tree
          (nodes_arr___arr_update
            (ob_tree___nodes___rcd_element tree )
            previous
            (node___right___rcd_update
              (nodes_arr___arr_element
                (ob_tree___nodes___rcd_element tree )
                previous
              )
              (node___left___rcd_element
                (nodes_arr___arr_element
                  (ob_tree___nodes___rcd_element tree )
                  x_node
                )
              )
            )
          )
        )
        previous
      )
      (- (size_of tree previous ) 1 )
    )
  )
  :status unknown
)
