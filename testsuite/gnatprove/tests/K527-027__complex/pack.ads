package Pack is

   type T1 is private; -- in Alfa
   type T2 is private; -- not in Alfa

   type P1 is new Integer;

   function PP1 return Boolean
     with Post => PP1'Result;

   function PP2 return Boolean
     with Post => PP2'Result;

private
   pragma SPARK_Mode (Off);
   type P2 is access Integer;
   type T1 is record
      X : P1;
   end record;
   type T2 is record
      X : P2;
   end record;

end Pack;
