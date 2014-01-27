pragma SPARK_Mode;
procedure No_Return_A (X : in     Integer;
                       Y :    out Integer)
is
   procedure Halt is
   begin
      loop
         null;
      end loop;
   end Halt;
begin
   if X > 0 then
      Y := X;
   else
      Halt;
   end if;
   Y := Y / 2;
end No_Return_A;
