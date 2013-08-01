package body Clock
   with Refined_State => (State => Current_Time)
is

   Current_Time : Time.T;

   procedure Initialise_To_Zero
     with Refined_Global => (Output => Current_Time)
   is
   begin
      Current_Time := Time.Zero;
   end Initialise_To_Zero;

   procedure Increment
     with Refined_Global => (In_Out => Current_Time)
   is
   begin
      Current_Time := Time.T_Increment (Current_Time);
   end Increment;

   function Get_Current_Time return Time.T is (Current_Time)
     with Refined_Global => (Current_Time);

end Clock;
