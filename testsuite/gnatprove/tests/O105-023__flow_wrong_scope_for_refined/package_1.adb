package body Package_1
   with SPARK_Mode => On,
        Refined_State => (State => (State_Var_1,
                                    State_Var_2))
is

   State_Var_1 : Integer := 0;
   State_Var_2 : Integer := 1;

   ----------------------------------------------------------------------------
   -- Invariant
   ----------------------------------------------------------------------------
   function Invariant return Boolean
   is (State_Var_1 <= State_Var_2)
   with Refined_Global => (Input => (State_Var_1,
                                     State_Var_2));

   ----------------------------------------------------------------------------
   -- Update
   ----------------------------------------------------------------------------
   procedure Update
      with Refined_Global => (In_Out => (State_Var_1,
                                         State_Var_2))
   is
      -------------------------------------------------------------------------
      -- Nested_Subprogram
      -------------------------------------------------------------------------
      procedure Nested_Subprogram
      with Global => (Input  => (State_Var_2),
                      In_Out =>  State_Var_1),
           Pre    => (Invariant),
           Post   => (Invariant)
      is
      begin
         State_Var_1 := State_Var_1 + 1;
      end Nested_Subprogram;

   begin
      Nested_Subprogram;
      State_Var_2 := State_Var_2 + 1;

   end Update;

end Package_1;
