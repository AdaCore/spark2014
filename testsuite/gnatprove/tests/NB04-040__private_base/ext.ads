with Base; use Base;

package Ext with
  SPARK_Mode
is
   type U is new T with private;

private
   type U is new T with record
      D : Integer;
   end record;

   function Sum (X : U) return Integer is (T(X).Sum + X.D);

   function Create (C : Integer) return U is (T'(Create (C)) with D => 0);

   procedure Test;
end Ext;
