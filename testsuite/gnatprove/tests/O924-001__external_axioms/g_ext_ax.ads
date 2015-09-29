generic
package G_Ext_Ax with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);
   type T1 is private;
   type T2 is new Integer;

private
   type T1 is new Integer;
end G_Ext_Ax;
