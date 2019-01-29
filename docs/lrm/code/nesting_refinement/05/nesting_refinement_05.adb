package body Nesting_Refinement_05
--# own State is X, Y;     -- Refined State
is
   X, Y: Integer;

   procedure Operate_On_State
   --# global in out X;    -- Refined Global
   --#           out Y;
   is
      Z: Integer;

      procedure Add_Z_To_X
      --# global in out X;
      --#        in     Z;
      is
      begin
	 X := X + Z;
      end Add_Z_To_X;

      procedure Overwrite_Y_With_Z
      --# global    out Y;
      --#        in     Z;
      is
      begin
	 Y := Z;
      end Overwrite_Y_With_Z;
   begin
      Z := 5;
      Add_Z_To_X;
      Overwrite_Y_With_Z;
   end Operate_On_State;

begin -- Promised to initialize State
      -- (which consists of X and Y)
   X := 10;
   Y := 20;
end Nesting_Refinement_05;
