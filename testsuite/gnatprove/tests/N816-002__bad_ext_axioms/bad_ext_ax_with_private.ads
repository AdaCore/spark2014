package Bad_Ext_Ax_With_Private with SPARK_Mode is
   pragma Annotate (GNATProve, External_Axiomatization);
   type T is private;
   function Add (X, Y : T) return T;
private
   type T is new Natural;
   function Add (X, Y : T) return T is (X + Y);
end Bad_Ext_Ax_With_Private;
