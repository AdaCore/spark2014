procedure Chained_Contract_Calls with SPARK_Mode is
   package A is
      type T is tagged null record;
      function Label (X : T) return Integer is (0);
      function Copy (X : T) return T is (X);
      procedure P (X : T) is null with Post'Class => Label (X) = Label (Copy (X));
   end A;
   use A;
   package B is
      type U is new T with null record;
      overriding function Label (X : U) return Integer is (1);
      overriding function Copy (X : U) return U is (X);
      overriding procedure P (X : U) is null;
   end B;
   use B;
   X : constant T'Class := U'(null record);
begin
   P (X);
   pragma Assert (False); --@ASSERT:FAIL
end Chained_Contract_Calls;
