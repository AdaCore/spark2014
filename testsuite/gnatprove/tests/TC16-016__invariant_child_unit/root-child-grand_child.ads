package Root.Child.Grand_Child with SPARK_Mode is
   type Grand_Child_T is private;
   function OK return Grand_Child_T;--@INVARIANT_CHECK:PASS
   function OK2 return Child_T;--@INVARIANT_CHECK:PASS
   function OK3 return Root_T;--@INVARIANT_CHECK:PASS
   function Bad return Grand_Child_T;--@INVARIANT_CHECK:FAIL
   function Bad2 return Child_T;--@INVARIANT_CHECK:FAIL
   function Bad3 return Root_T;--@INVARIANT_CHECK:FAIL
   function Bad4 return Child_T;--@INVARIANT_CHECK:FAIL
   function Bad5 return Root_T;--@INVARIANT_CHECK:FAIL
private
   type Grand_Child_T is new Integer with
     Default_Value => 0,
     Type_Invariant => Grand_Child_T >= 0;
   function Priv return Grand_Child_T is (-1);
   function OK return Grand_Child_T is (Priv + 2);
   function Priv2 return Child_T is (-1);
   function OK2 return Child_T is (Priv + 2);
   function Priv3 return Root_T is (-1);
   function OK3 return Root_T is (Priv + 2);
   function Bad return Grand_Child_T is (Priv);
   function Bad2 return Child_T is (Priv);
   function Bad3 return Root_T is (Priv);
   function Bad4 return Child_T is (Priv2);
   function Bad5 return Root_T is (Priv3);
end Root.Child.Grand_Child;
