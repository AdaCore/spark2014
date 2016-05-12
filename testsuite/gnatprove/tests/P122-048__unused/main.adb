with Ada.Text_IO;

procedure Main (J : Integer; K : in out Integer) is

   pragma Unreferenced (J);         --  Valid
   pragma Unused (K);               --  Valid

   --  Improper use
   Z : Boolean := False;
   pragma Unreferenced (Z);         --  Valid

   --  Proper use
   A, B, C, D : Boolean := True;

   G : Boolean;

   type Rec is
      record
	 E : Boolean;
	 F : Boolean;
      end record;

   R : Rec := (E => True,
	       F => True);

   pragma Unmodified (A);           --  Valid
   pragma Unreferenced (B);         --  Valid
   pragma Unmodified (C);           --  Valid
   pragma Unreferenced (C);         --  Valid
   pragma Unused (D);               --  Valid
   pragma Unreferenced (R);
   pragma Unreferenced (G);

begin

   G := R.E;
   Z := A;                          --  Valid
   B := False;                      --  Valid

end Main;
