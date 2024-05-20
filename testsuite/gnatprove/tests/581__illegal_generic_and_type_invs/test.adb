with Inst;
procedure Test with SPARK_Mode is

   --  Instance outside Inst are rejected

   procedure My_PP is new Inst.PP;
   package My_Nested is new Inst.Nested;
begin
  null;
end Test;
