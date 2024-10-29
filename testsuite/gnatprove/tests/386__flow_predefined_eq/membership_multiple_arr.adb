procedure Membership_Multiple_Arr with SPARK_Mode is

   type R is record A : Integer; end record;

   function "=" (X, Y : R) return Boolean;

   type R2 is record
      F : R;
   end record;

   subtype SR2 is R2 with Predicate => SR2.F.A in 0 | 1;

   type R2_Arr is array (Positive range <>) of R2;

   function F return Boolean is
      X : R2;
      Arr : R2_Arr (1 .. 2);
   begin
      return X in SR2 | Arr (1);
   end F;

   function "=" (X, Y : R) return Boolean is (F);

   B : Boolean := F;

begin
   null;
end Membership_Multiple_Arr;
