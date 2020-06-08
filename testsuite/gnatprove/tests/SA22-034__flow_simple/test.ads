package Test
with
   Abstract_State => State, Initializes => State
is

   subtype Index_Type is Natural range 0 .. 123;

private

   function Root return Index_Type with Global => State;

   Count : array (Index_Type) of Natural
     := (others => 0)
   with
      Part_Of => State;

   procedure Clear (I : Index_Type)
   with
      Post => Root = Root'Old, Global => (In_Out => State);

end Test;
