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

end P;
