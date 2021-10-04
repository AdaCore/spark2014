package body Repr with
  SPARK_Mode
is

   procedure Initialize (Buffer : out Bytes_Ptr)
   is
   begin
      Buffer := null;
   end Initialize;

end Repr;
