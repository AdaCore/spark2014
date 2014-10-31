with Parent.Child_1;

package body Parent
  with Refined_State => (State => H_State)
is
   pragma SPARK_Mode;

   H_State : Boolean;

   procedure Initialise
     with Refined_Global => (Output => (H_State,
                                        Parent.Child_1.State))
   is
   begin
      H_State := False;
      Child_1.Initialise;
   end Initialise;


end parent;
