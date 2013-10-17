package body Volatiles_Illegal_14
  with SPARK_Mode
is
   procedure P (Par : out Vol_Rec_T) is
   begin
      Par.X := 5;
   end P;
begin
   P (Vol);  --  Vol does not have Async_Readers and
             --  Effective_Writes set to True.
end Volatiles_Illegal_14;
