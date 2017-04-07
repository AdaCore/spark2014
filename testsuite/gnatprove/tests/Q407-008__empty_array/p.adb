procedure P (Limit : Integer) with SPARK_Mode, Global => null is

   subtype Num is Positive range 1 .. Limit;

   type A is array (Num) of Num;

   C : A := (others => 1);

begin
   null;
end;
