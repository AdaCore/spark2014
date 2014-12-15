with Notag_Base; use Notag_Base;

package Notag_Ext with
  SPARK_Mode
is
   type U is new T;

   function Sum (X : U) return Integer is (Sum(T(X)));

   function Create (C : Integer) return U is (U(T'(Create (C))));

   procedure Test;
end Notag_Ext;
