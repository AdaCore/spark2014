procedure Main with SPARK_Mode is
   type T is array (Integer range 1 .. 10) of Integer;
   A : T := (others => 0);

   procedure Test (X : Integer) with Pre => True is
      B : Integer renames A (X);  -- @INDEX_CHECK:FAIL
   begin
      null;
   end Test;

   procedure Test2 (X : Integer; A : T) with
     Pre => True,
     Relaxed_Initialization => A
   is
      B : Integer renames A (X);  -- @INDEX_CHECK:FAIL @INIT_BY_PROOF:NONE
   begin
      null;
   end Test2;

   procedure Test3 (X : Integer; A : T) with
     Pre => True,
     Relaxed_Initialization => A
   is
      B : Integer renames A(A(X));  -- @INDEX_CHECK:FAIL @INIT_BY_PROOF:FAIL
   begin
      null;
   end Test3;

begin
   Test (11); -- intentionally out-of-bound
end Main;
