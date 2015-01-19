package Array_Logical_Ops is
   pragma SPARK_Mode (On);

   subtype My_Boolean is Boolean range False .. True;

   type Bool_Array is array (Integer range <>) of My_Boolean;

   subtype Only_True is Boolean range True .. True;

   type True_Array is array (Integer range <>) of Only_True;

   procedure Test_Ok1;

   procedure Test_Ok2;

   procedure Test_Ok3;

   procedure Test_Ok4;

   procedure Test_Ok5;

   procedure Failing_Length_Check (Z : Bool_Array);

   procedure Failing_Content_Check;

end Array_Logical_Ops;
