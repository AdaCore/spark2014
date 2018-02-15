with Bad;

package Util is
   protected type P is
      entry E_01
        with Max_Queue_Length => Bad.X;

   private
      Flag : Boolean := False;
   end P;

   PO : P;
end Util;
