package Bad_Ext_Ax_With_Body with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);
   type T is new Natural;
   function Add (X, Y : T) return T with
     Pre => T'Last - X <= Y;
end Bad_Ext_Ax_With_Body;
