procedure Main with SPARK_Mode is

   package Nested is
      type R is tagged record
         F : Integer;
      end record;
      type C is new R with record
         G : Integer;
      end record;
   end Nested;
   use Nested;

   type Small is tagged record
      F : Integer;
   end record;
   type Big is tagged record
      F : Integer;
      G : Integer;
   end record;

   procedure PR (X : in out R) with Pre => True is
      Y : Small with Import, Address => X'Address;
   begin
      pragma Assert (Y'Size = X'Size);
   end PR;

   procedure PC (X : in out C) with Pre => True is
      Y : Big with Import, Address => X'Address;
   begin
      pragma Assert (Y'Size = X'Size);
   end PC;

   procedure PRC (X : in out R'Class) with Pre => True is
      Y : Small with Import, Address => X'Address; --  failed size check
   begin
      null;
   end PRC;

   XR : R := (F => 1);
   XC : C := (1, 2);
begin
   PR (XR);
   PR (R (XC));
end Main;
