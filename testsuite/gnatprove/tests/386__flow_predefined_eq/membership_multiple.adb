procedure Membership_Multiple with SPARK_Mode is

   type R is record A : Integer; end record;

   function "=" (X, Y : R) return Boolean;

   type R2 is record
      F : R;
   end record;

   subtype SR2 is R2 with Predicate => SR2.F.A in 0 | 1;

   function F return Boolean is
      X, Y : R2;
   begin
      return X in SR2 | Y;
   end F;

   function "=" (X, Y : R) return Boolean is (F);

   B : Boolean := F;

begin
   null;
end Membership_Multiple;