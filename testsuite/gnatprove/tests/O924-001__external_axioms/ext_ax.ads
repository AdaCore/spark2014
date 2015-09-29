with G_Ext_Ax;
package Ext_Ax is
   pragma Annotate (GNATprove, External_Axiomatization);
   type T1 is private;
   type T2 is new Integer;

   package P is new G_Ext_Ax;

private
   type T1 is new Integer;
end Ext_Ax;
