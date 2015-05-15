with Ada.Text_IO; use Ada.Text_IO;

package body Stacks is

   procedure Push (S : in out Stack; E : Element) is
   begin
      if S.Is_Full then
         return;
      end if;

      S.Top := S.Top + 1;
      S.Data (S.Top) := E;
   end Push;

   procedure Pop (S : in out Stack) is
   begin
      if S.Is_Empty then
        return;
      end if;

      S.Top := S.Top - 1;
   end Pop;

   procedure Print (S : Stack) is
   begin
      Put ('[');
      for J in reverse 1 .. S.Top loop
         Put (Element'Image (S.Data (J)));
      end loop;
      Put (" ]");
   end Print;

end Stacks;
