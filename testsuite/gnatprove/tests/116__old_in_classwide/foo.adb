procedure Foo with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F : Integer;
      end record;

      procedure Swap (X, Y : in out Root) with
        Post'Class => X = Y'Old and Y = X'Old;

      type Child is new Root with record
         G : Integer;
      end record;

      procedure Swap (X, Y : in out Child);

   end Nested;
   package body Nested is

      procedure Swap (X, Y : in out Root) is
         Tmp_F : constant Integer := X.F;
      begin
         X.F := Y.F;
         Y.F := Tmp_F;
      end Swap;

      procedure Swap (X, Y : in out Child) is
         Tmp_G : constant Integer := X.G;
      begin
         X.G := Y.G;
         Y.G := Tmp_G;
         Swap (Root (X), Root (Y));
      end Swap;

   end Nested;
   use Nested;

   C1 : Child := (1, 2);
   RC1 : Root'Class := C1;
   C2 : Child := (1, 2);
   RC2 : Root'Class := C2;
begin
   Swap (RC1, RC2);
end Foo;
