package P_Main
  with
    SPARK_Mode => On
is
 function Id (X : Integer) return Integer is (X);

   subtype T is Integer range Id (1) .. Id (-1);

   function F return Boolean is (True) with
     Post => C = Id (3) and then False;

   C : constant T := Id (3); --@RANGE_CHECK:FAIL
   type TT is private with Default_Initial_Condition => F;
   B : constant Boolean := F;

private
   type TT is record
      F : T := C;
   end record;
end P_Main;
