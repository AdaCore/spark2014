package Const is

   --  logic constants

   A : constant Integer := 1;
   B : constant Integer := 1;

   type TC is array (1 .. 2) of Integer;
   C  : constant TC := (others => 1);
   C2 : constant TC := TC'(others => 1);
   --  C3 : constant TC := TC(TC'(others => Natural(1)));
   D  : constant TC := (1, 1);
   D2 : constant TC := TC'(1, 1);
   --  D3 : constant TC := TC(TC'(1, 1));

   type TE is record X, Y: Integer; end record;
   E : constant TE := (others => 1);
   F : constant TE := (1, 1);
   G : constant TE := TE'(1, 1);
   --  H : constant TE := TE(TE'(1, 1));

   function FI return Integer is (1);
   I : constant Integer := FI;
   J : constant Integer := 2 * FI - 1;

   function FK return Integer is (B);
   K : constant Integer := FK;
   L : constant Integer := 2 * FK - 1;

   function FM (X : Integer) return Integer is (X);
   M : constant Integer := FM (1);
   N : constant Integer := 2 * FM (B) - 1;

   --  not logic constants

   O : Integer := 1;
   P : constant Integer := FM (O);

   procedure Test;

end Const;
