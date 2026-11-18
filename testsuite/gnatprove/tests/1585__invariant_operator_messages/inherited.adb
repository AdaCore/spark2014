procedure Inherited with SPARK_Mode is
   package Base is
      type T is tagged record
         Value : Integer;
      end record;

      function "&" (Left, Right : Integer) return T is
        (Value => Integer'Max (Left, Right));
   end Base;

   package Derived is
      type T is new Base.T with null record --@PREDICATE_CHECK:FAIL
        with Predicate => Value >= 0;
   end Derived;
begin
   null;
end Inherited;
