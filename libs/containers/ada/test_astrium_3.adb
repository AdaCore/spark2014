package body Test_Astrium_3 is

   procedure Activate_First_Non_Active (L : in out List) is
      Cu : Cursor := First(L);
   begin
      while Has_Element(Cu) loop
         if not Is_Active(Element(Cu)) then
            exit;
         end if;
         Next(Cu);
      end loop;

      if (Has_Element(Cu)) then
         Replace_Element (L, Cu, Activate(Element(Cu)));
      end if;
   end Activate_First_Non_Active;

end Test_Astrium_3;
