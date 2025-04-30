procedure Contract_Call_On_Result with SPARK_Mode is
   package A is
      type T is tagged null record;
      function F (X : T) return Integer is (0);
      function Copy (X : T) return T with Post'Class => F (Copy'Result) = F (X);
      function Copy (X : T) return T is (X);
   end A;
   use A;
   package B is
      type U is new T with null record;
      overriding function F (X : U) return Integer is (1);
      overriding function Copy (X : U) return U is (X);
   end B;
   X : T'Class := B.U'(null record);
begin
   X := Copy (X);
   pragma Assert (False); --@ASSERT:FAIL
end Contract_Call_On_Result;
