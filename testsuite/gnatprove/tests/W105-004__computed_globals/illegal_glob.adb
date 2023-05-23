procedure Illegal_Glob with SPARK_Mode is

   --  Higher_Order_Specialization applied to procedure with a global out

   Global_V : Integer;

   procedure Proc_Out_Global (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization);

   procedure Proc_Out_Global (F : not null access function return Integer) is
   begin
      Global_V := F.all;
   end Proc_Out_Global;
begin
   null;
end Illegal_Glob;
