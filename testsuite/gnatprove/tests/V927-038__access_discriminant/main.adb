procedure Main
with SPARK_Mode => On
is
   type Nat_Array is array (Positive range <>) of Natural;
   type R (D : Integer) is record
      F : Nat_Array (1 .. D);
   end record;

   type R_Acc is not null access all R;

   procedure Set (X : R_Acc; Y : R) with Pre => True is
   begin
      X.all := Y; -- @DISCRIMINANT_CHECK:FAIL
   end Set;
begin
    null;
end Main;
