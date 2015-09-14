with Ada.Dispatching;

package body P is

   protected body PO is
      entry Yielding_Entry when True is
      begin
         Ada.Dispatching.Yield;
      end;
   end;

end;
