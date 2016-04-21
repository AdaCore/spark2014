with Ada.Text_IO;

procedure Main is

   --  Improper use
   X, Y, Z : Boolean := False;

   --  Proper use
   A, B, C, D : Boolean := True;
   pragma Unmodified (A);           --  Valid
   pragma Unreferenced (B);         --  Valid
   pragma Unmodified (C);           --  Valid
   pragma Unreferenced (C);         --  Valid
   pragma Unused (D);               --  Valid

begin
   Z := A;                          --  Valid
   B := False;                      --  Valid
end Main;
