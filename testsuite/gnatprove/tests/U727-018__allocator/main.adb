with Interfaces; use Interfaces;
procedure Main with SPARK_Mode is
   package Nested is
      type T (<>) is private;
      type T_Acc is access all T;
   private
      function Id (X : Integer) return Integer is (X);
      type T is new Integer range Id (1) .. 15 with Default_Value => 0; --@RANGE_CHECK:FAIL
      X : T_Acc := new T;
   end Nested;
   package Nested_2 is
      type T is private;
      type T_Acc is access all T;
   private
      function Id (X : Integer) return Integer is (X);
      type T is new Integer range Id (1) .. 15;
      X : T_Acc := new T'(0); --@RANGE_CHECK:FAIL
   end Nested_2;
begin
  null;
end;
