package Root.Child with SPARK_Mode is
   type Child_T is private;
   function OK return Child_T;--@INVARIANT_CHECK:PASS
   function OK2 return Root_T;--@INVARIANT_CHECK:PASS
   function Bad return Child_T;--@INVARIANT_CHECK:FAIL
   function Bad2 return Root_T;--@INVARIANT_CHECK:FAIL
   function Bad3 return Root_T;--@INVARIANT_CHECK:FAIL
private
   type Child_T is new Integer with
     Default_Value => 0,
     Type_Invariant => Child_T >= 0;
   function Priv return Child_T is (-1);
   function OK return Child_T is (Priv + 2);
   function Bad return Child_T is (Priv);
   function Priv2 return Root_T is (-1);
   function OK2 return Root_T is (Priv + 2);
   function Bad2 return Root_T is (Priv);
   function Bad3 return Root_T is (Priv2);
end Root.Child;
