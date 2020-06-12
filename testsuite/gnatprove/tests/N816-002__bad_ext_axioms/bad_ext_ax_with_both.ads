package Bad_Ext_Ax_With_Both with SPARK_Mode is
   pragma Annotate (GNATProve, External_Axiomatization);
   type T is private;
   function Add (X, Y : T) return T;
private
   type T is new Natural;
end Bad_Ext_Ax_With_Both;
