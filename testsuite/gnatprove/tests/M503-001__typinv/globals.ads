package Globals with
  SPARK_Mode,
  Abstract_State => (State_X, State_Y)
is

   type T is private;

   procedure Abs_Create  --  @INVARIANT_CHECK:PASS
     with Global => (Output => State_Y);

   procedure Abs_Update  --  @INVARIANT_CHECK:PASS
     with Global => (In_Out => State_Y);

   function Abs_Get return Integer
     with Global => (Input => State_Y);

   procedure Gen_Create;  --  @INVARIANT_CHECK:PASS

   procedure Gen_Update;  --  @INVARIANT_CHECK:PASS

   function Gen_Get return Integer;

   procedure Abs_Gen_Create;  --  @INVARIANT_CHECK:PASS

   procedure Abs_Gen_Update;  --  @INVARIANT_CHECK:PASS

   function Abs_Gen_Get return Integer;

private

   type T is new Integer with
     Default_Value => 42,
     Type_Invariant => T /= 0;

   X : T with Part_Of => State_X;

   procedure Create  --  @INVARIANT_CHECK:PASS
     with Global => (Output => X);

   procedure Update  --  @INVARIANT_CHECK:PASS
     with Global => (In_Out => X);

   function Get return Integer
     with Global => (Input => X);

end Globals;
