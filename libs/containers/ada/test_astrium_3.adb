package body Test_Astrium_3 is

   function Is_Active (E : Boolean) return Boolean is
   begin
      return E;
   end Is_Active;

   function Activate (E : Boolean) return Boolean is
   begin
      return True;
   end Activate;

   function Weight (E : Boolean) return Integer is
   begin
      if Is_Active(E) then
         return 1;
      else
         return 0;
      end if;
   end Weight;

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
