with Initialization_And_Elaboration.Private_Child;
pragma Elaborate (Initialization_And_Elaboration.Private_Child);
--  pragma Elaborate for the private child is required because it is a
--  constituent of the state abstraction
--  Initialization_And_Elaboration.State, which is mentioned in the
--  Initializes aspect of the package.

package body Initialization_And_Elaboration
  with Refined_State => (State => Private_Child.State)
  --  State is initialized
  --  Private child must be elaborated.
is
   procedure Do_It (I : in Integer)
     with Refined_Global => (In_Out => Private_Child.State)
   is
   begin
      Private_Child.Do_Something (I);
   end Do_It;

   function Get_It return Integer
     with Refined_Global => Private_Child.State
   is
   begin
      return Private_Child.Get_Something;
   end Get_It;
end Initialization_And_Elaboration;
