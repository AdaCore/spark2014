package Check_Default_Value with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   package P is
      type T is private;
      function Is_OK (X : T) return Boolean;
   private
      One : constant Natural := Id (1);
      subtype My_Positive is Natural range One .. Natural'Last;

      type T is new My_Positive with Default_Value => 0; --@RANGE_CHECK:FAIL
      function Is_OK (X : T) return Boolean is (X = 0);
   end P;

   subtype S is P.T;
   X : S;
end Check_Default_Value;
