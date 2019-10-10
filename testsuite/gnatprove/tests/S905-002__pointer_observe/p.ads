package P with SPARK_Mode is

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function With_Side_Effect (X : List_Acc) return access constant List
     with Pre => True;

end P;
