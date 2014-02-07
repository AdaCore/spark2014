procedure No_Return_B (X : in     Integer;
                       Y :    out Integer)
  with SPARK_Mode
is
   procedure Halt with No_Return;

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
end No_Return_B;
