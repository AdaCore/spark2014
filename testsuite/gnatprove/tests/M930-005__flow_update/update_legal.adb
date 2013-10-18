package body Update_Legal
  with SPARK_Mode
is
   procedure P1 (Arr : in out Array_T) is
   begin
      Arr := Arr'Update (1 .. 5 => True,
                         2 .. 5 => False,
                         3 .. 5 => True,
                         4 .. 5 => False,
                         5 => True);
      --  When array ranges overlap then the initial ones are
      --  overwritten by the subsequent ones.
      pragma Assert (Arr(1) and
                     not Arr(2) and
                     Arr(3) and
                     not Arr(4) and
                     Arr(5));
   end P1;
end Update_Legal;
