package body My_Types with SPARK_Mode is

   procedure Incr (X : in out My_Root) is
   begin
      if X.F < Integer'Last then
         X.F := X.F + 1;
      end if;
   end Incr;
end My_Types;
