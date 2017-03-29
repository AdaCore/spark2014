

with Ada.Text_IO;

package body Generic_Parent is

   procedure Print( This: in out Object ) is
   begin
       -- Ada.Text_IO.Put_Line("A: " & Element'Image(This.A));

       This.Increment;
   end Print;

   use type Element;
   procedure Increment( This: in out Object ) is

       Step: Element := Element'(1);
   begin
       if This.A <= Element'Last - Step then
           This.A := This.A + Step;
       end if;
   end Increment;

end Generic_Parent;
