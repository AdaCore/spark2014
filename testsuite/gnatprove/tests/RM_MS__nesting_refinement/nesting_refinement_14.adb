package body Nesting_Refinement_14
  -- State is refined onto two concrete variables X and Y
  with SPARK_Mode,
       Refined_State => (State => (X, Y))
is
   X, Y: Integer;

   procedure Operate_On_State
     with Refined_Global => (In_Out => X,
                             Output => Y)
   is
      Z: Integer;

      procedure Add_Z_To_X
        with Global => (In_Out => X,
                        Input  => Z)
      is
      begin
         X := X + Z;
      end Add_Z_To_X;

      procedure Overwrite_Y_With_Z
        with Global => (Output => Y,
                        Input  => Z)
      is
      begin
         Y := Z;
      end Overwrite_Y_With_Z;
   begin
      Z := 5;
      Add_Z_To_X;
      Overwrite_Y_With_Z;
   end Operate_On_State;

begin
   -- Promised to initialize State
   -- (which consists of X and Y)
   X := 10;
   Y := 20;
end Nesting_Refinement_14;
