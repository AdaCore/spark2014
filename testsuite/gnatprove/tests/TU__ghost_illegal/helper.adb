package body Helper is
   function Return_First (A, B : Elem ; Choice : Boolean) return Elem is
   begin
      if Choice then
         return A;
      else
         return B;
      end if;
   end Return_First;
end Helper;
