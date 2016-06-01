package Globals with
  Abstract_State => (State_X, State_Y)
is

   type T is private;

   procedure Abs_Create
     with Global => (Output => State_X);

   procedure Abs_Update
     with Global => (In_Out => State_X);

   function Abs_Get return Integer
     with Global => (Input => State_X);

   procedure Gen_Create;

   procedure Gen_Update;

   function Gen_Get return Integer;

   procedure Abs_Gen_Create;

   procedure Abs_Gen_Update;

   function Abs_Gen_Get return Integer;

private

   type T is new Integer with
     Default_Value => 42,
     Type_Invariant => T /= 0;

   X : T with Part_Of => State_X;

   procedure Create
     with Global => (Output => X);

   procedure Update
     with Global => (In_Out => X);

   function Get return Integer
     with Global => (Input => X);

end Globals;
