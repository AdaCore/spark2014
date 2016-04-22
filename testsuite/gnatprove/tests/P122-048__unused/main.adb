with Ada.Text_IO;

procedure Main (J : Integer; K : in out Integer) is

   pragma Unreferenced (J);         --  Valid
   pragma Unused (K);               --  Valid

   --  Improper use
   Z : Boolean := False;
   pragma Unreferenced (Z);         --  Valid

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
