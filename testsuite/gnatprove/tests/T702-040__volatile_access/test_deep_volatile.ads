package Test_Deep_Volatile with SPARK_Mode is
   type Int_Ptr is access Integer;

   X : Int_Ptr with Volatile, Async_Readers;

   procedure Test1;

   procedure Test2;

   procedure Test3;

   procedure Test4;

   function Test5 return Int_Ptr with Volatile_Function;

   procedure P (X : in out Int_Ptr) is null;

   procedure Test6;
end Test_Deep_Volatile;
