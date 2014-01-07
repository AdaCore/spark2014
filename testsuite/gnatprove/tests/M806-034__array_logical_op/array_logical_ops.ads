package Array_Logical_Ops is
   pragma SPARK_Mode (On);

   subtype My_Boolean is Boolean range False .. True;

   type Bool_Array is array (Integer range <>) of My_Boolean;

   subtype Only_True is Boolean range True .. True;

   type True_Array is array (Integer range <>) of Only_True;

   procedure P;

end Array_Logical_Ops;
