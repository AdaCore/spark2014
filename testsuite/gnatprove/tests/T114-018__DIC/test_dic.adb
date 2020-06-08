procedure Test_DIC (C : Natural) with SPARK_Mode is
   package Nested is
      type T (X : Boolean := False) is private with
        Default_Initial_Condition => (if X then C /= 0);
   private
      type T (X : Boolean := False) is record
         case X is
         when True =>
            F : Positive := C; --@RANGE_CHECK:PASS
         when False =>
            null;
         end case;
      end record;
   end Nested;
   use Nested;

   X : T (False); --@DEFAULT_INITIAL_CONDITION:PASS
   Y : T; --@DEFAULT_INITIAL_CONDITION:PASS
   Z : T (True); --@DEFAULT_INITIAL_CONDITION:FAIL
begin
   null;
end Test_DIC;
