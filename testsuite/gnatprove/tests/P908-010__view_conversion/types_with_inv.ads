package Types_With_Inv with SPARK_Mode is
   type T1 is new Integer with Default_Value => 1;

   procedure Set_To_Zero (X : out T1);

   type T2 is private;

   procedure Test (X : in out T2);  --@INVARIANT_CHECK:FAIL

   procedure Test2 (X : in out T2);  --@INVARIANT_CHECK:FAIL

   type R1 is record
      F : Integer := 1;
   end record;

   procedure Set_To_Zero (X : out R1);

   type R2 is private;

   procedure Test (X : in out R2);  --@INVARIANT_CHECK:FAIL

   procedure Test2 (X : in out R2);  --@INVARIANT_CHECK:FAIL
private
   type T2 is new T1 with
     Default_Value  => 1,
     Type_Invariant => T2 /= 0;

   type R2 is new R1 with
     Type_Invariant => R2.F /= 0;
end Types_With_Inv;
