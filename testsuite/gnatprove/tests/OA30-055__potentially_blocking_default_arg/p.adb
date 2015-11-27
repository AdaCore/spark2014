with Ada.Dispatching;

package body P is

   function Blocking return Boolean is
   begin
      Ada.Dispatching.Yield;
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
