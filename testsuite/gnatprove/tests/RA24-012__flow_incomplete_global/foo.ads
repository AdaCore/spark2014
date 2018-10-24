package Foo
with
   Abstract_State => State,
   Elaborate_Body
is

   type State_Type is private;

   function Get_State return State_Type
   with
      Global => (Input => State),
      Ghost;

   function Check (S : State_Type) return Boolean
   with
      Global => (Input => State),
      Ghost;

   function Valid (S : State_Type) return Boolean
   with
      Ghost;

private

   type State_Type is array (Integer range 0 .. 100) of Boolean;

   State_Var : State_Type := (others => False)
   with
      Part_Of => State;

   function Get_State return State_Type
   is (State_Var);

   function Check (S : State_Type) return Boolean
   is (True);

   function Valid (S : State_Type) return Boolean
   is (Check (S));

end Foo;
