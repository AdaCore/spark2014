package body P is
   pragma SPARK_Mode (Off);

   function Init return T is
      A : T;
   begin
      return A;
   end Init;

   function Get (X : T) return T is (X);
end P;

