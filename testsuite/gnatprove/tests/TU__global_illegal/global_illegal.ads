package Global_Illegal
  with SPARK_Mode,
       Abstract_State => (A1,
                          A2,
                          A3,
                          A4,
                          A5,
                          (A6 with External => Async_Writers),
                          (A7 with External),
                          (A8 with External => Async_Readers),
                          (A9 with External => (Async_Readers,
                                                Async_Writers)))
is
   type Rec is
      record
         A, B : Integer;
      end record;

   type Tab is array (1 .. 10) of Integer;
   Table : Tab;
   First_Element : Integer renames Table (1);

   X, Y : Integer;
   Z    : Integer renames X;
   Comp : Rec;


   package Internal_Package
     with Global => X  --  incorrect placement of global aspect
   is
   end Internal_Package;


   procedure P1 (Par : Integer)
     --  TU: 4. A ``global_item`` shall denote an entire object or a state
     --  abstraction.
     --  [This is a name resolution rule because a ``global_item`` can
     --  unambiguously denote a state abstraction even if a function having the
     --  same fully qualified name is also present].
     with Global => (Comp.A,         --  global_item is not a stand alone
                                     --  variable

                     Non_Existant);  --  global_item is neither a variable
                                     --  nor a state abstraction


   procedure P2 (Par : Integer)
     --  TU: 9. Each ``mode_selector`` shall occur at most once in a single
     --  Global aspect.

     --  TU: 6. A ``global_item`` occurring in a Global aspect specification of
     --  a subprogram shall not denote a formal parameter of the subprogram.
     with Global => (In_Out   => A1,    --  OK
                     Input    => A2,    --  OK
                     Output   => A3,    --  OK
                     Proof_In => A4,    --  OK
                     In_Out   => A5,    --  duplicate In_Out mode selector
                     Input    => X,     --  duplicate Input mode selector
                     Output   => Comp,  --  duplicate Output mode selector
                     Proof_In => Y,     --  duplicate Proof_In mode selector
                     Output   => Par);  --  defining_identifier matches formal
                                         --  parameter


   procedure P3 (Par : Integer)
     --  TU: 11. The ``global_items`` in a single Global aspect specification
     --  shall denote distinct entities.
     with Global => (Input  => X,   --  OK
                     Output => X,   --  variable referenced twice in a single
                                    --  Global aspect
                     In_Out => Z);  --  same variable referenced (via a
                                    --  variable that uses renames)


   procedure P4 (Par : Integer)
     --  TU: ::
     --  global_specification     ::= (moded_global_list {, moded_global_list})
     --                             | global_list
     --                             | null_global_specification
     --  moded_global_list         ::= mode_selector => global_list
     --  global_list               ::= global_item
     --                              | (global_item {, global_item})
     --  mode_selector             ::= Input | Output | In_Out | Proof_In
     --  global_item               ::= name
     --  null_global_specification ::= null
     with Global => (A1, null, A2);  --  cannot have both null and other
                                      --  abstract states in a single global
                                      --  statement

   procedure P5
     with Global => First_Element;  --  global_item is not a stand alone
                                    --  variable

   function F1 (Par : Integer) return Integer
     --  TU: 10. A function subprogram shall not have a ``mode_selector`` of
     --  Output or In_Out in its Global aspect.
     with Global => (Output => A1,   --  function has Output as mode_selector
                     In_Out => A2);  --  function has In_Out as mode_selector
end Global_Illegal;
