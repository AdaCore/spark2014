package Check_Component_Default_Value with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   package P is
      type T (<>) is private;
   private
      One : constant Natural := Id (1);
      subtype My_Positive is Natural range One .. Natural'Last;
      type T is array (Positive range <>) of My_Positive with
        Default_Component_Value => 0; --@RANGE_CHECK:FAIL

      X : T (1 .. 2);
   end P;
end Check_Component_Default_Value;
