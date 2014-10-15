package Foo
with
   SPARK_Mode,
   Abstract_State => State,
   Initializes    => State
is

   function Get_Data return Natural
   with
      Global => (Input => State);

   procedure Set_Data (Data : Natural)
   with
      Global  => (Output => State),
      Depends => (State => Data);

end Foo;
