procedure Membership_Func with SPARK_Mode is

   type R is record A : Integer; end record;

   function "=" (X, Y : R) return Boolean;

   type R2 is record
      F : R;
   end record;

   function F return Boolean is
      X, Y : R2;
      function Foo return R2 with Import;
   begin
      return X in Foo;
   end F;

   function "=" (X, Y : R) return Boolean is (F);

   B : Boolean := F;

begin
   null;
end Membership_Func;
