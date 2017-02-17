package P is

   type T is mod 16;

   function F (X : T) return Integer with
     Pre  => X = 15,
     Post => F'Result = 17;
   --  This postcondition is incorrect

   function G (X : T) return Integer with
     Pre  => X = 15,
     Post => G'Result = 1;
   --  This postcondition is correct

   function M return Integer
     with Post => (M'Result = 16);

   function Id (X : T) return T
      with Post => (Id'Result = X);
end P;
