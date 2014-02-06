pragma SPARK_Mode;
procedure No_Return_B (X : in     Integer;
                       Y :    out Integer)
is
   procedure Halt with No_Return is
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
