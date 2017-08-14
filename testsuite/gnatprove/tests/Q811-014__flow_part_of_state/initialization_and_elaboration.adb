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
   procedure Init (I : in Integer)
     with Refined_Global => (Output => Private_Child.State)
   is
   begin
      Private_Child.Init (I);
   end Init;

   function Get_It return Integer
     with Refined_Global => Private_Child.State
   is
   begin
      return Private_Child.Get;
   end Get_It;
end Initialization_And_Elaboration;
