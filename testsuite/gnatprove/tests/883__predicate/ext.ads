package Ext with SPARK_Mode is
   type T is private;
   function P (X : T) return Boolean with Import;
private
   type T is record
      F, G : Integer;
   end record with Predicate => F < G;
end Ext;
