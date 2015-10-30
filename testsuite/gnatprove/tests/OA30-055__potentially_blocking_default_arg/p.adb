with Ada.Real_Time; use type Ada.Real_Time.Time;

package body P is

   function Blocking return Boolean is
   begin
      delay until Ada.Real_Time.Clock;
      return True;
   end;

   protected body PO is
      entry Dummy (Arg : Boolean := Blocking) when True is
         pragma Unreferenced (Arg);
      begin
         null;
      end;
   end;

end;
