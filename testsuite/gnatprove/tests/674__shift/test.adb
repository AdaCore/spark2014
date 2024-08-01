with Interfaces; use Interfaces;

procedure Test with SPARK_Mode is
   procedure Add (X : in out Unsigned_8; B : Boolean) is
   begin
      X := X * 2 + (if B then 1 else 0);
      pragma Assert (B = (Shift_Right (X, 0) mod 2 = 1));
   end Add;

   package Nested is
      type Uns_8 is private;

      procedure Add (X : in out Uns_8; B : Boolean);
   private

      type Uns_8 is new Unsigned_8;
   end Nested;

   package body Nested is
      procedure Add (X : in out Uns_8; B : Boolean) is
      begin
         X := X * 2 + (if B then 1 else 0);
         pragma Assert (B = (Shift_Right (X, 0) mod 2 = 1));
      end Add;
   end Nested;
begin
   null;
end Test;
