package Ext_2 with SPARK_Mode is
   type T_Acc is private;

private
   type T is tagged;
   type T_Acc is access T;

   --  Early usage in specification is rejected

   package P is
      function F (X : T) return Integer;
      function G (X : Integer) return T;
   end P;

end Ext_2;
