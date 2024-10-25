procedure Primitive_Eq with SPARK_Mode is

   type R is null record;

   function "=" (X, Y : R) return Boolean;

   type R2 is record
      F : R;
   end record;

   function F return Boolean is
      X, Y : R2;
   begin
      return X = Y;
   end F;

   function "=" (X, Y : R) return Boolean is (F);

   B : Boolean := F;

begin
   null;
end Primitive_Eq;
