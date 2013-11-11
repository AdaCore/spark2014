package body Global_Illegal_3
  with SPARK_Mode
is
   --  TU: 16. Each entity denoted by a ``global_item`` in a
   --  ``global_specification`` of a subprogram that is an input or
   --  output of the subprogram shall satisfy the following mode
   --  specification rules [which are checked during analysis of the
   --  subprogram body]:
   --  * a ``global_item`` that denotes an input but not an output has a
   --    ``mode_selector`` of Input;
   --  * a ``global_item`` has a ``mode_selector`` of Output if:
   --    - it denotes an output but not an input, other than the use of a
   --      discriminant or an attribute related to a property, not its
   --      value, of the ``global_item`` [examples of attributes that may
   --      be used are A'Last, A'First and A'Length; examples of
   --      attributes that are dependent on the value of the object and
   --      shall not be used are X'Old and X'Update] and
   --    - is always *fully initialized* (that is, all parts of the
   --      ``global_item`` are initialized) as a result of any successful
   --      execution of a call of the subprogram. A state abstraction
   --      whose refinement is not visible is not fully initialized by
   --      only updating one or more of its constituents [because it may
   --      have other constituents that are not visible];
   --  * otherwise the ``global_item`` denotes both an input and an output,
   --    and has a ``mode_selector`` of In_Out.

   procedure P1 (Par1 : out Integer)
     --  TU: 13. For a subprogram that has a ``global_specification``, an
     --  object or state abstraction that is declared outside the scope of the
     --  subprogram, shall only be referenced within its implementation if
     --  it is a ``global_item`` in the ``global_specification``.
     with Global => X
   is
   begin
      Par1 := X + Y;
   end P1;


   procedure P2
     --  TU: 1. A ``global_specification`` that is a ``global_list`` is
     --  shorthand for a ``moded_global_list`` with the ``mode_selector``
     --  Input.
     with Global => X
   is
   begin
      X := 10;
   end P2;


   procedure P3
     --  TU: 3. A ``null_global_specification`` indicates that the subprogram
     --  does not reference any ``global_item`` directly or indirectly.
     with Global => null
   is
   begin
      X := 10;
   end P3;


   procedure P4
     --  TU: 14. A ``global_item`` shall occur in a Global aspect of a
     --  subprogram if and only if it denotes an entity that is referenced by
     --  the subprogram.
     with Global => X
   is
   begin
      null;
   end P4;


   procedure P5
     --  TU: [For purposes of determining whether an output of a subprogram
     --  shall have a ``mode_selector`` of Output or In_Out, reads of array
     --  bounds, discriminants, or tags of any part of the output are ignored.
     --  Similarly, for purposes of determining whether an entity is fully
     --  initialized as a result of any successful execution of the call", only
     --  nondiscriminant parts are considered. This implies that given an
     --  output of a discriminated type that is not known to be constrained
     --  ("known to be constrained" is defined in Ada RM 3.3), the
     --  discriminants of the output might or might not be updated by the
     --  call.]
     with Global => (Input  => X,
                     Output => Y,
                     In_Out => Z)
   is
   begin
      null;
   end P5;


   procedure P6
     --  TU: [For purposes of determining whether an output of a subprogram
     --  shall have a ``mode_selector`` of Output or In_Out, reads of array
     --  bounds, discriminants, or tags of any part of the output are ignored.
     --  Similarly, for purposes of determining whether an entity is fully
     --  initialized as a result of any successful execution of the call", only
     --  nondiscriminant parts are considered. This implies that given an
     --  output of a discriminated type that is not known to be constrained
     --  ("known to be constrained" is defined in Ada RM 3.3), the
     --  discriminants of the output might or might not be updated by the
     --  call.]
     with Global => (Input  => X,
                     Output => (Y, Arr),
                     In_Out => Z)
   is
   begin
      X := Y;
      Z := 5 + Arr'First;
   end P6;


   procedure P7
     --  TU: 17. An entity that is denoted by a ``global_item`` which is
     --  referenced by a subprogram but is neither an input nor an output but
     --  is only referenced directly, or indirectly in assertion expressions
     --  has a ``mode_selector`` of Proof_In.
     with Global => (Output   => Y,
                     Proof_In => X)
   is
   begin
      pragma Assert (X > 5);
      Y := X;
   end P7;


   procedure P8
     with Global => (Proof_In => X)
   is
   begin
      null;
   end P8;


   procedure P9
     with Global => (Output => Arr2)
   is
   begin
     Arr2 (1) := 10;
   end P9;
end Global_Illegal_3;
