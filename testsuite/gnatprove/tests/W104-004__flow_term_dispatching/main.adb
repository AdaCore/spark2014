with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

procedure Main with SPARK_Mode is
   procedure Foo (A, B : Unbounded_String) with Always_Terminates
   is
      C : Boolean := A = B;
   begin
      null;
   end Foo;
begin
   null;
end Main;
