with Use_Cst;
procedure Use_Indirect_Cst
  with SPARK_Mode
is
   procedure Local with Pre => True is
   begin
      Use_Cst.P;
   end Local;
begin
   Local;
end Use_Indirect_Cst;
