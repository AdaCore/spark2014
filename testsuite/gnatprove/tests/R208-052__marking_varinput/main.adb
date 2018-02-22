with P;

procedure Main with SPARK_Mode Is
   type T is array (p.cpu_number) of Integer;
   -- This array type is not in SPARK, because its index type is not

   type R is record
      C : T := (others => 0);
   end record;
   --  This record type is not in SPARK, because its component has a type that
   --  is not in SPARK; rejecting it because of "(others => 0)" in default
   --  expression, which causes a dependence on variable input via an array
   --  bound, is too late and gives a hard to understand error.

begin
   null;
end;
