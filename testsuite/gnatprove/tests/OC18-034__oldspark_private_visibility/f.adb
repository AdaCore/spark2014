with BT;
with BT.O;

package body F
is

   --  This is originally an oldspark ticket, but its good to sanity check
   --  that there are no similar visibility issues in spark 2014...

   function V (X : in R1) return Boolean
   is
      Y : BT.MyP;
   begin
      Y := BT.O.SF (X.F1);
      return Y = 2;
   end V;

end F;
