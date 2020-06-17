package Bad_Ext_Ax with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);
   type T is new Natural;
   function Add (X, Y : T) return T is (X + Y) with
     Pre => T'Last - X <= Y;
end Bad_Ext_Ax;
