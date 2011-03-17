package body Count is
   pragma Annotate (Formal_Proof, On);
   function Count (Max : Integer; Step : Natural) return Natural is
      Res : Natural := 0;
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
