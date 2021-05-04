package Root with SPARK_Mode is
   type Root_T is private;
   function OK return Root_T;--@INVARIANT_CHECK:PASS
   function Bad return Root_T;--@INVARIANT_CHECK:FAIL
   procedure P;--@INVARIANT_CHECK:NONE
   procedure Q;--@INVARIANT_CHECK:PASS
private
   type Root_T is new Integer with
     Default_Value => 0,
     Type_Invariant => Root_T >= 0;
   function Priv return Root_T is (-1);
   function OK return Root_T is (Priv + 2);
   function Bad return Root_T is (Priv);
end Root;
