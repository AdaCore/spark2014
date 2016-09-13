package Typeinv with SPARK_Mode is 
   type T is private;

   function New_T (X : Integer) return T;

   procedure Divide (X : in out T); -- @INVARIANT_CHECK:FAIL

private
   type T is range 0 .. 10000 --@INVARIANT_CHECK:FAIL
      with Type_Invariant => Is_Valid (T);

   function Is_Valid (X : T) return Boolean is
      (X mod 2 = 0);

end Typeinv;
