package body Test is
   procedure if_1 (Par1 : in out Integer) is
   begin
      if Par1 > 1000 then
         Par1 := 999;
      elsif Par1 > 100 then
         Par1 := 99;
      elsif Par1 > 10 then
         Par1 := 9;
      else
         Par1 := 0;
      end if;
   end if_1;

   procedure if_2 (Par1 : in out Integer) is
   begin
      if Par1 > 1000 then
         Par1 := 999;
      elsif Par1 > 100 then
         Par1 := 99;
      end if;
   end if_2;

   procedure if_3 (Par1 : in out Integer) is
   begin
      if Par1 > 1000 then
         Par1 := 999;
      else
         Par1 := 0;
      end if;
   end if_3;

   procedure if_4 (Par1 : in out Integer) is
   begin
      if Par1 > 1000 then
         Par1 := 999;
      end if;
   end if_4;

   procedure case_1 (Par1 : Integer; Par2 : out Integer) is
   begin
      case Par1 is
         when 1 =>
            Par2 := 1;
         when 2 | 3 =>
            Par2 := 2;
         when 4 .. 10 =>
            Par2 := 3;
         when others =>
            Par2 := 4;
      end case;
   end case_1;
end Test;
