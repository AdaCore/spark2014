
package Pred with SPARK_Mode is
   type T is private;
   function Get (X : T) return Integer;

   type T_Ptr is private;
   function Bad_New_T return T_Ptr; --@INVARIANT_CHECK:FAIL
   function Ok_New_T return T_Ptr; --@INVARIANT_CHECK:PASS
private
   type T is new Integer with Type_Invariant => T >= 0, Default_Value => 0;
   type Holder is record
      Content : T;
   end record;
   type T_Ptr is access Holder;

   function Priv_New_T return T_Ptr; --@INVARIANT_CHECK:NONE

   function Get (X : T) return Integer is (Integer (X));

   function Bad_New_T return T_Ptr is (new Holder'(Content => -1));
   function Ok_New_T return T_Ptr is (new Holder'(Content => 1));
   function Priv_New_T return T_Ptr is (new Holder'(Content => -1));
end;
