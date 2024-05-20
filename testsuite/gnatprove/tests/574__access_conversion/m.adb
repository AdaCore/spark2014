procedure M with SPARK_Mode is
   function F return Boolean is (True) with SPARK_Mode => Off;

   package Nested is
      type X is private;
      procedure P1 (C : in out X);
   private
      type X is not null access Integer with Predicate => F;
   end Nested;

   package body Nested is
      procedure P2 (C : not null access Integer) with
        Global => null;
      procedure P2 (C : not null access Integer) is
      begin
         C.all := 13;
      end P2;

      procedure P1 (C : in out X) is
      begin
         P2 (C);
      end P1;
   end Nested;
begin
   null;
end M;
