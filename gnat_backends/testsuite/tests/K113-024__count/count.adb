package body Count is
   function Count (Max : Integer; Step : Integer) return Integer is
      Res : Integer := 0;
   begin
      loop
         Res := Res + Step;
         if Res > Max then
            exit;
         end if;
      end loop;
      return Res;
   end Count;
end Count;
