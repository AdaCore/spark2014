package body P is
   type T (D : Integer := 0) is record
      C : Integer;
   end record;

   X : T;

   procedure Write is
   begin
      X := (D => 1, C => 0);
   end;

   Y : T (1);

   procedure Read_Write is
   begin
      Y := (D => 1, C => 0);
   end;

   procedure Main is
   begin
      P.Write;
      P.Write;

      P.Read_Write;
      P.Read_Write;
   end;
end;
