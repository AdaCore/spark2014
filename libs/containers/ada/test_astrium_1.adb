package body Test_Astrium_1 is

   function Test_Recovery (L : List) return Recovery_T is
      Cu : Cursor := First(L);
   begin
      while Has_Element(Cu) loop
         if Detects_Failure(Element(Cu)) then
            return Reboot;
         end if;

         Next(Cu);
      end loop;

      return None;
   end Test_Recovery;

end Test_Astrium_1;
