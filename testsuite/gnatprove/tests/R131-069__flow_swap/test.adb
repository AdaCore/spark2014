with Ada.Text_IO; use Ada.Text_IO;

procedure Test with SPARK_Mode is

   procedure Swap (X, Y : in out Boolean) is
      Tmp : constant Boolean := X;  -- should by Y
   begin
      Y := X;
      X := Tmp;
   end Swap;

   A : Boolean := True;
   B : Boolean := not A;

begin
   Swap (A, B);
   Put_Line (Boolean'Image (A) & ", " & Boolean'Image (B));
end Test;
