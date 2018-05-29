package body P is

   function Target return Integer with Pre => True;

   function Generic_Proxy return Integer is
   begin
      return Target;
   end;

   D : Integer := 0;

   function Identity (X : Integer) return Integer is (X)
      with Pre =>True, SPARK_Mode => Off;

   function Target return Integer is
   begin
      return 1/Identity (D);
   end;

end;
