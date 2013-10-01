package Depends_Illegal
  with SPARK_Mode,
       Abstract_State => ((A1 with External => Async_Writers),
                          (A2 with External => Async_Readers))
is
   type Int_Arr is array (1 .. 10) of Integer;

   type Rec is
      record
         A, B : Integer;
      end record;

   X, Y, Z : Integer;
   Comp : Rec;


   procedure P1 (Par1 : in out Integer ; Par2 : Int_Arr)
     --  TU: 1. An ``input`` or ``output`` of a ``dependency_relation`` shall
     --  denote only an entire object or a state abstraction. [This is a name
     --  resolution rule because an ``input`` or ``output`` can unambiguously
     --  denote a state abstraction even if a function having the same fully
     --  qualified name is also present.]

     --  TU: 8. Every member of the explicit input set of a subprogram shall be
     --  denoted by at least one ``input`` of the ``dependency_relation`` of
     --  the subprogram.

     --  TU: 10. Every member of the output set of a subprogram shall be
     --  denoted by exactly one ``output`` in the ``dependency_relation`` of
     --  the subprogram.
     with Global  => (Output => Comp),
          Depends => (Par1   => Par2(5),  --  input is not an entire object
                      Comp.A => Par1,     --  output is not an entire object
                      X      => Y);       --  not a state abstraction or
                                          --  formal parameter of the
                                          --  subprogram


   procedure P2 (Par1, Par3 : Integer ; Par2, Par4 : out Integer)
     --  TU: 4. The *explicit input set* of a subprogram is the set of formal
     --  parameters of the subprogram of mode **in** and **in out** along with
     --  the entities denoted by ``global_items`` of the Global aspect of the
     --  subprogram with a ``mode_selector`` of Input and In_Out.

     --  TU: 6. The *output set* of a subprogram is the set of formal
     --  parameters of the subprogram of mode **in out** and **out** along with
     --  the entities denoted by ``global_items`` of the Global aspect of the
     --  subprogram with a ``mode_selector`` of In_Out and Output and (for a
     --  function) the ``function_result``.

     --  TU: 7. The entity denoted by each ``input`` of a
     --  ``dependency_relation`` of a subprogram shall be a member of the input
     --  set of the subprogram.

     --  TU: 9. The entity denoted by each ``output`` of a
     --  ``dependency_relation`` of a subprogram shall be a member of the
     --  output set of the subprogram.
     with Global  => (Input  => X,
                      Output => (Y, Z)),
          Depends => (Par1 =>  X,     --  Par1 isn't of mode "out" or "in out"
                      Y    =>  Par2,  --  input isn't of mode "in" or "in out"
                      Z    =>+ X);    --  entity of both input and output
                                      --  should have mode "in out"


   function F1 (Par1 : in Integer) return Integer
     --  TU: 6. The *output set* of a subprogram is the set of formal
     --  parameters of the subprogram of mode **in out** and **out** along with
     --  the entities denoted by ``global_items`` of the Global aspect of the
     --  subprogram with a ``mode_selector`` of In_Out and Output and (for a
     --  function) the ``function_result``.
     with Depends => (null => (Par1, F1'Result)); -- F1'Result cannot appear
                                                  -- as an input


   procedure P3 (Par1 : out Integer ; Par2 : Integer)
     --  TU: 12. In a ``dependency_relation`` there can be at most one
     --  ``dependency_clause`` which is a ``null_dependency_clause`` and if
     --  it exists it must be the last ``dependency_clause`` in the
     --    ``dependency_relation``.

     --  TU: 10. Every member of the output set of a subprogram shall be
     --  denoted by exactly one ``output`` in the ``dependency_relation`` of
     --  the subprogram.

     --  TU: 13. An entity denoted by an ``input`` which is in an
     --  ``input_list`` of a ``null_dependency_clause`` shall not be denoted by
     --  an ``input`` in another ``input_list`` of the same
     --  ``dependency_relation``.
     with Global  => (Input  => A1,
                      Output => A2),
          Depends => (Par1 => A1,  --  an input of an input_list of a null
                                   --  export may not appear in another
                                   --  input_list
                      null => A1,  --  a null output_list must be the last
                                   --  dependency_clause in the
                                   --  dependency_relation
                      null => Par2);  --  there can be at most one null
                                      --  output_list in a dependency_relation


   procedure P4 (Par1 : Integer)
     --  TU: 13. An entity denoted by an ``input`` which is in an
     --  ``input_list`` of a ``null_dependency_clause`` shall not be denoted by
     --  an ``input`` in another ``input_list`` of the same
     --  ``dependency_relation``.
     with Global  => (Output => X),
          Depends => (X    => Par1,   --  Par1 is an input of a null
                                      --  output_list (so it cannot appear
                                      --  here)
                      null => Par1);  --  OK


   procedure P5 (Par1 : out Integer ; Par2 : in Integer)
     --  TU: 14. The ``inputs`` in a single ``input_list`` shall denote
     --  distinct entities.
     with Global  => (Output  => X),
          Depends => ((Par1, X, Par1) => Par2);  --  same object denoted twice
                                                 --  in a single output_list


   procedure P6 (Par1, Par2 : out Integer)
     --  TU: 10. Every member of the output set of a subprogram shall be
     --  denoted by exactly one ``output`` in the ``dependency_relation`` of
     --  the subprogram.
     with Global  => (Input  => (X, Y)),
          Depends => (Par1 => X,   --  OK
                      Par1 => Y);  --  output appears in more than one
                                   --  output_list
                                   --  output (Par2) does not appear in
                                   --  any output_list


   procedure P7 (Par1 : out Integer)
     --  TU: 8. Every member of the explicit input set of a subprogram shall be
     --  denoted by at least one ``input`` of the ``dependency_relation`` of
     --  the subprogram.
     with Global  => (Input  => (X, Y)),
          Depends => (Par1 => X);  --  OK
                                   --  input (Y) does not appear in any
                                   --  input_list


   --  TU: ::
   --     dependency_relation    ::= null
   --                             | (dependency_clause {, dependency_clause})
   --     dependency_clause      ::= output_list =>[+] input_list
   --                              | null_dependency_clause
   --     null_dependency_clause ::= null => input_list
   --     output_list            ::= output
   --                              | (output {, output})
   --     input_list             ::= input
   --                              | (input {, input})
   --                              | null
   --     input                  ::= name
   --     output                 ::= name | function_result
   --  where
   --     ``function_result`` is a function Result ``attribute_reference``.
   procedure P8 (Par1 : Integer)
     with Depends => (null =>+ Par1);  --  =>+ holds no meaning for a null
                                       --  output_list


   procedure P9 (Par1 : Integer ; Par2 : in out Integer)
     with Depends => (Par2 =>+ (Par1, null));  --  cannot have null and other
                                               --  inputs


   procedure P10
     --  TU: 15. A ``null_dependency_clause`` shall not have an ``input_list``
     --  of **null**.
     with Depends => (null => null);
end Depends_Illegal;
