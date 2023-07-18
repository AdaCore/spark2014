procedure Info_Msg with SPARK_Mode is
   procedure Callee with
     Pre => True,
     Always_Terminates => False;

   procedure Callee is
   begin
      null;
   end;

   procedure Caller with
     Always_Terminates;

   procedure Caller is
   begin
      Callee;
   end Caller;
begin
   null;
end Info_Msg;
