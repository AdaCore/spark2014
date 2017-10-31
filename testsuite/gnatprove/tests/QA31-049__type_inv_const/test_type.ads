package Test_Type with SPARK_Mode, Initializes => null is
   type T is private;
   X : constant T;
private
   type T is record
      F : Integer := 0;
   end record
     with Type_Invariant => F in Natural;

   X : constant T := (F => -1); --  @INVARIANT_CHECK:FAIL
end Test_Type;
