package body Parent.Child_1
  with Refined_State => (State => H_State)
is
   pragma SPARK_Mode;

   H_State : Integer;

   procedure Initialise
     with Refined_Global => (Output => H_State)
   is
   begin
      H_State := 0;
   end Initialise;

end Parent.Child_1;
