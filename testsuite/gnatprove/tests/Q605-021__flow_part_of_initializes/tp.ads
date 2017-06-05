with Ext;

package TP
   with Initializes => (B4 => null)
is
   B4 : Integer := Ext.Var
     with Part_Of => Singl_Prot;

   protected Singl_Prot is
   end Singl_Prot;

end TP;
