procedure Test with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F : Integer;
      end record;
      procedure P (X : in out Root) with
        Post'Class => X.F = X.F'Old;
      type Child is new Root with record
         G : Integer;
      end record;
      procedure P (X : in out Child);
   end Nested;
   package body Nested is
      procedure P (X : in out Root) is null;
      procedure P (X : in out Child) is
      begin
         X.G := 0;
      end P;
   end Nested;
   use Nested;

   X : Root'Class := Root'Class (Child'(1, 2));
begin
   pragma Assert (Child (X).G = 2);
   P (X);
   pragma Assert (Child (X).G = 2); -- @ASSERT:FAIL
end Test;
