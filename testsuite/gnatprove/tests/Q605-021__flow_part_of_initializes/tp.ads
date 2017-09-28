with Ext;

package TP
   with Initializes => (B4 => null)
is
   protected Singl_Prot is
   end Singl_Prot;

   B4 : Integer := Ext.Var
     with Part_Of => Singl_Prot;

end TP;
