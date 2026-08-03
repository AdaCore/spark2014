package body Orig
  with SPARK_Mode
is

   function Generic_Make_T return T
   is ((Default_T with delta X => 1));

   --  Intentionally violate the predicate on T
   function Make_T return T is
      function Impl is new
        Generic_Make_T (Default_T => (X => 0));  --@PREDICATE_CHECK:FAIL
   begin
      return Impl;
   end Make_T;

end Orig;
