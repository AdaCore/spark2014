package body Dynamic_Preds is

   procedure Do_Nothing (X : Bad) with SPARK_Mode is
   begin
      null;
   end Do_Nothing;

   procedure Do_Nothing (X : Bad_Pair) with SPARK_Mode is
   begin
      null;
   end Do_Nothing;

   procedure Do_Nothing (X : Bad_Array) with SPARK_Mode is
   begin
      null;
   end Do_Nothing;

   package body Local
     with SPARK_Mode
   is
      procedure Do_Nothing (X : Bad) with SPARK_Mode is
      begin
         null;
      end Do_Nothing;

      procedure Do_Nothing (X : Bad_Pair) with SPARK_Mode is
      begin
         null;
      end Do_Nothing;

      procedure Do_Nothing (X : Bad_Array) with SPARK_Mode is
      begin
         null;
      end Do_Nothing;
   end Local;
end Dynamic_Preds;
