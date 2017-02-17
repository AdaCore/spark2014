package Stack_External_Prover
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => Is_Empty
is
   --  A Ghost function may be an Import which means that no body is
   --  given in the SPARK 2014 code and the proof has to be discharged
   --  by an external prover. Of course, such functions are not
   --  executable.
   function Max_Stack_Size return Natural
     with Global     => null,
          Ghost,
          Import;

   --  Returns the number of elements on the stack
   function Count return Natural
     with Global     => (Input => State),
          Ghost,
          Import;

   --  Returns the Nth entry on the stack. Stack_Entry (Count) is the
   --  top of stack
   function Stack_Entry (N : Natural) return Integer
     with Global     => (Input => State),
          Ghost,
          Import;

   function Is_Empty return Boolean
     with Global     => State,
          Ghost,
          Import;

   function Is_Full return Boolean
     with Global     => State,
          Ghost,
          Import;

   procedure Push (X : in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full,
          Post   => Count = Count'Old + 1 and Count <= Max_Stack_Size and
                    Stack_Entry (Count) = X;

   procedure Pop (X : out Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty,
          Post   => Count = Count'Old - 1;

   procedure Swap2
     with Global => (In_Out => State),
          Pre    => Count >= 2,
          Post   => Count = Count'Old and
                    Stack_Entry (Count) = Stack_Entry (Count - 1)'Old and
                    Stack_Entry (Count - 1) = Stack_Entry (Count)'Old;
end Stack_External_Prover;
