with System;
package P
is

   protected PO is
      pragma Priority (System.Default_Priority); -- ceiling priority protocol is respected
      procedure Dummy;
   private
      X : Boolean := False;
   end;


end;
