package body Length_Others
  with SPARK_Mode
is
   procedure Init (S : out Bytes) is
   begin
      S := (others => 0);
   end Init;
end Length_Others;
