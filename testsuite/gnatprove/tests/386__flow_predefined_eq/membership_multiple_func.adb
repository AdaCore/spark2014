procedure Membership_Multiple_Func with SPARK_Mode is

   type R is record A : Integer; end record;

   function "=" (X, Y : R) return Boolean;

   type R2 is record
      F : R;
   end record;

   subtype SR2 is R2 with Predicate => SR2.F.A in 0 | 1;

   function F return Boolean is
      X : R2;
      function Foo return R2 with Import, Global => null;
   begin
      return X in SR2 | Foo;
   end F;

   function "=" (X, Y : R) return Boolean is (F);

   B : Boolean := F;

begin
   null;
end Membership_Multiple_Func;
