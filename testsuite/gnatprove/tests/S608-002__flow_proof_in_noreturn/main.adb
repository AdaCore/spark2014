with Ada.Text_IO;
with Run;

procedure Main with
   SPARK_Mode
is

   X : Integer := 1;

   procedure Load with
      No_Return,
      Pre    => X /= 0,
      Global => (Proof_In => X)
   is
   begin
      Run;
   end Load;

begin
   Ada.Text_IO.Put_Line ("hello " & Integer'Image (X));
end Main;
