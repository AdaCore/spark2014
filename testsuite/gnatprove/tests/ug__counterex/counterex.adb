procedure Counterex (Cond : Boolean; In1, In2 : Integer; R : out Integer) with
  SPARK_Mode,
  Pre => In1 <= 25 and In2 <= 25
is
begin
   R := 0;
   if Cond then
      R := R + In1;
      if In1 < In2 then
         R := R + In2;
         pragma Assert (R < 42);
      end if;
   end if;
end Counterex;
