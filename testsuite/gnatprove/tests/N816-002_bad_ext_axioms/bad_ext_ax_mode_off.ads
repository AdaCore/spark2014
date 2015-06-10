package Bad_Ext_Ax_Mode_Off with SPARK_Mode => Off is
   type T is new Natural;
   function Add (X, Y : T) return T is (X + Y) with
     Pre => T'Last - X <= Y;
end Bad_Ext_Ax_Mode_Off;
