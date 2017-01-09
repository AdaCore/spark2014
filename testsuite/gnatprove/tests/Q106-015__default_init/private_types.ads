package Private_Types with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   package P4 is
      type T2 is private;
   private
      One : constant Natural := Id (1);
      subtype My_Positive is Natural range One .. Natural'Last;

      type T2 is new My_Positive with Default_Value => 0; --@RANGE_CHECK:FAIL
   end P4;

   Y4 : P4.T2;
end Private_Types;
