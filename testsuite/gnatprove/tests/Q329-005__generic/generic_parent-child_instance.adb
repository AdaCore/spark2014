

with Ada.Text_IO;

package body Generic_Parent.Child_Instance is

   overriding
   procedure Print( This: in out Object ) is
   begin
       -- Ada.Text_IO.Put_Line( "A: " & Element'Image(This.A) &
       --                       " B: " & Element'Image(This.B));

       This.Increment;
   end Print;

   overriding
   procedure Increment( This: in out Object ) is

       Step: Element := Element'(1);
   begin
       if This.A <= Element'Last - Step then
           This.A := This.A + Step;
       end if;

       if This.B >= Element'First + Step then
           This.B := This.B - Step;
       end if;
   end Increment;

end Generic_Parent.Child_Instance;
