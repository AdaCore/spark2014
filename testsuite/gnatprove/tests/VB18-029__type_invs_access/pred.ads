
package Pred with SPARK_Mode is
   type T is private;
   type T_Ptr is access T;
   function Bad_New_T return T_Ptr; --INVARIANT_CHECK:FAIL
   function OK_New_T return T_Ptr; --INVARIANT_CHECK:PASS
private
   type T is new Integer with Type_Invariant => T >= 0, Default_Value => 0;

   function Priv_New_T return T_Ptr; --INVARIANT_CHECK:NONE

   function Bad_New_T return T_Ptr is (new T'(-1));
   function OK_New_T return T_Ptr is (new T'(1));
   function Priv_New_T return T_Ptr is (new T'(-1));
end;
