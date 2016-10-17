procedure Foo (Secret : Integer;
               Y      : out Integer)
is

   package Nested with
      Initializes => (V => null,
                      W => Secret),
      Initial_Condition => (V = 0)
   is
      V : Integer := Secret;
      W : Integer := Secret;
   end Nested;

   Tmp : constant Integer := Nested.V;

   package body Nested is
   begin
      V := 0;
   end Nested;

begin

   Y := Tmp;

end Foo;
