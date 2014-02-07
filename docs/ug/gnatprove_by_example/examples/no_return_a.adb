procedure No_Return_A (X : in     Integer;
                       Y :    out Integer)
  with SPARK_Mode
is
   procedure Halt;

   procedure Halt is
   begin
      loop
         null;
      end loop;
   end Halt;
begin
   if X <= 0 then
      Halt;
   end if;
   Y := X / 2;
end No_Return_A;
