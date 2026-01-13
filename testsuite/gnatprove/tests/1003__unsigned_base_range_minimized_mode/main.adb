pragma Extensions_Allowed (All_Extensions);

procedure Main with SPARK_Mode is
   type U is range 0 .. 2 ** 32 - 1 with Unsigned_Base_Range;

   function Id (X : U) return U is (X);
   function Pre_OK (X, Y : U) return Boolean is (True) with Pre => X + Y <= U'Last; --@OVERFLOW_CHECK:PASS
   function Pre_KO (X, Y : U) return Boolean is (True) with Pre => X * X * Y <= U'Last; --@OVERFLOW_CHECK:FAIL

   procedure Test_Assert;
   procedure Test_Code;
   procedure Test_Assert is
      Y : constant U := Id (2000000000);
      Z : constant U := Id (3000000000);
      B : constant Boolean := Pre_KO (Y,Z);
      C : constant Boolean := Pre_KO (Y, Z);
   begin
      null;
   end Test_Assert;
   procedure Test_Code is
      X : constant U := Id (2000000000);
      Y : constant U := Id (3000000000);
      Z : constant U := X + Y - Id (1000000000); --@OVERFLOW_CHECK:FAIL
   begin
      null;
   end Test_Code;

   function Logarithm (X, Y : U) return U
     with Global => null,
     Pre => X >= Y
     and then (X * X - Y * Y = 1 + Y * Y
               or else (X * X + 1) - Y * Y = Y * Y),
     Post => Logarithm'Result <= Y;
   --  Compute L such that X + Y * sqrt (2) = (1 + sqrt(2)) ** L
   --  Works with minimized mode, the intermediate multiplication results
   --  fits in 64-bits unsigned integers.

   function Logarithm (X, Y : U) return U is
      X_i : U := X;
      Y_i : U := Y;
      Lg  : U := 0;
   begin
      while Y_i /= 0 loop
         pragma Loop_Invariant (X_i >= Y_i);
         pragma Loop_Invariant
           (X_i * X_i - Y_i * Y_i = 1 + Y_i * Y_i
            or else (X_i * X_i + 1) - Y_i * Y_i = Y_i * Y_i);
         pragma Loop_Invariant (Lg + Y_i <= Y);
         pragma Loop_Variant (Decreases => X_i);

         --  Uses (sqrt(2) - 1)(sqrt(2) + 1) = 1.
         --  (X_i + Y_i * sqrt (2)) * (sqrt (2) - 1)
         --  = (2 * Y_i - X_i) + sqrt (2) * (X_i - Y_i)
         Y_i := X_i - Y_i;

         --  Y_(i+1) = X_i - Y_i <-> Y_i = X_i - Y_(i+1),
         --  (2 * Y_i - X_i) = (2 * (X_i - Y_(i+1)) - X_i)
         --                  = X_i - 2 * Y_(i+1)
         X_i := X_i - 2 * Y_i;
         Lg := Lg + 1;
      end loop;
      return Lg;
   end Logarithm;
   L : constant U := Logarithm (3, 2);

   function Logarithm_KO (X, Y : U) return U
     with Global => null,
     Pre => X >= Y
     and then (X * X - 2 * Y * Y = 1
               or else (X * X + 1) - 2 * Y * Y = 0),
     Post => Logarithm_KO'Result <= Y;
   --  Bad pre-condition, X * X - 2 * Y * Y might overflow

   function Logarithm_KO (X, Y : U) return U is
      X_i : U := X;
      Y_i : U := Y;
      Lg  : U := 0;
   begin
      while Y_i /= 0 loop
         pragma Loop_Invariant (X_i >= Y_i);
         pragma Loop_Invariant
           (X_i * X_i - Y_i * Y_i = 1 + Y_i * Y_i
            or else (X_i * X_i + 1) - Y_i * Y_i = Y_i * Y_i);
         pragma Loop_Invariant (Lg + Y_i <= Y);
         pragma Loop_Variant (Decreases => X_i);

         X_i := 2 * Y_i - X_i;
         --  Bad update order, 2 * Y_i may overflow the range of U.
         --  While that is actually vacuous because the largest power of
         --  (1 + sqrt(2)) that fits in 32-bits integer components is
         --  1855077841 + 1311738121 * sqrt(2) (25-th power), it would be
         --  highly unexpected for automated provers to figure it out.

         Y_i := Y_i - X_i;

         Lg := Lg + 1;
      end loop;
      return Lg;
   end Logarithm_KO;

begin
   null;
end Main;
