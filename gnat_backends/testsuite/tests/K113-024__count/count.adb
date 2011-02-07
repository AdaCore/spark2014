package body Count is
   function Count (Max : Integer; Step : Integer) return Integer is
      Res : Integer := 0;
   begin
      loop
         Pragma Assert (Res <= Max);
         Res := Res + Step;
         if Res > Max then
            exit;
         end if;
      end loop;
      return Res;
   end Count;
end Count;
