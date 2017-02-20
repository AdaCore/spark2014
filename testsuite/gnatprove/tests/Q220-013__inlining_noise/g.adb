package body G with SPARK_Mode => Off is

   Ptr : access Integer;

   function Is_Initialized return Boolean is
   begin
      return Ptr /= null;
   end;

   procedure Initialize is
   begin
      Ptr := null;
   end;

begin
   Initialize;
end G;
