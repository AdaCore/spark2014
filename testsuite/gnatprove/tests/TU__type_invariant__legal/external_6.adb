package body External_6 with SPARK_Mode is

   function Read (X : T) return Integer is
   begin
      return Pub (X);  --  @INVARIANT_CHECK:NONE
   end Read;

   procedure Read (X : T) is
   begin
      Pub_In (X);  --  @INVARIANT_CHECK:NONE
   end Read;

   procedure Write (X : out T) is
   begin
      Pub_Out (X);  --  @INVARIANT_CHECK:NONE
   end Write;

   procedure Read_Write (X : in out T) is
   begin
      Pub_In_Out (X);  --  @INVARIANT_CHECK:NONE
   end Read_Write;

end External_6;
