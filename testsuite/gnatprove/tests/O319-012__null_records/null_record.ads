package Null_Record with Spark_Mode is
   type Null_Rec is null record;
   subtype Null_Rec2 is Null_Rec;

   type T_Null_Rec is tagged null record;
   type T_Null_Rec2 is new T_Null_Rec with null record;

   procedure Check_Equal;
   procedure Check_Aggregate;
   procedure Check_Procedure_Call;
end Null_Record;
