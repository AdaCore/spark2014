package body Count is  
   pragma Annotate (gnatprove, Force);
   function Count (Max : Integer; Step : Natural) return Natural is
      Res : Natural := 0;
   begin
      loop
         pragma Loop_Invariant (Res <= Max);
         Res := Res + Step;
         if Res > Max then
            exit;
         end if;
      end loop;
      return Res;
   end Count;
end Count;
