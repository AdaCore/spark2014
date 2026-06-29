with SPARK.Containers.Functional.Total_Maps;

package Inst
  with SPARK_Mode
is
   function Equivalent (X, Y : Integer) return Boolean
   is (X mod 100 = Y mod 100);
   function Equal (X, Y : Integer) return Boolean
   is (X mod 1000 = Y mod 1000);
   package Int_Total_Maps is new
     SPARK.Containers.Functional.Total_Maps
       (Integer,
        Integer,
        0,
        Equivalent_Keys     => Equivalent,
        "="                 => Equal,
        Equivalent_Elements => Equivalent);
end Inst;
