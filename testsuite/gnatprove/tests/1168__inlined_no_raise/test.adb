procedure Test with SPARK_Mode is

   procedure P with No_Raise is
   begin
      raise Program_Error;
   end P;

   procedure Call_P with Exceptional_Cases => (others => True) is
   begin
      P;
   end Call_P;
begin
   null;
end;
