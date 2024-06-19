procedure Corner_Cases with SPARK_Mode is
   package A is
      type T is tagged private;
   private
      type U is tagged null record;
      function F return U is (null record);
      function G return U is (null record) with SPARK_Mode => Off;
      type T is new U with null record;
   end A;
begin
   null;
end Corner_Cases;
