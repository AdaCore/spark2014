procedure Main with SPARK_Mode is
   function Rand (X : Integer) return Boolean with Import;

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;
      function "=" (X, Y : Root) return Boolean is (X.F = Y.F);
      type Child is new Root with record
         G : Integer;
      end record;
      function "=" (X, Y : Child) return Boolean is (X.G = Y.G) with SPARK_Mode => Off;
      type Untagged is record
         F : Integer;
         G : Integer;
      end record;
      function "=" (X, Y : Untagged) return Boolean is (X.G = Y.G) with SPARK_Mode => Off;
   end Nested;
   use Nested;

   type Holder is record
      C : Untagged;
   end record;

   C1  : Child := (1, 2);
   C2  : Child := (2, 2);
   H1  : Holder := (C => (1, 2));
   H2  : Holder := (C => (2, 2));
   CC1 : Root'Class := C1;
   CC2 : Root'Class := C2;
begin
   if Rand (1) then
      pragma Assert (H1 = H2);
   elsif Rand (2) then
      pragma Assert (H1 /= H2);
   elsif Rand (3) then
      pragma Assert (CC1 = CC2);
   elsif Rand (4) then
      pragma Assert (CC1 /= CC2);
   end if;
end;
