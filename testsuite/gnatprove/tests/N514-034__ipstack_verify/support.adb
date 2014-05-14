package body Support with
  SPARK_Mode => Off
is
   procedure Verify (B : Boolean) is
   begin
      if not B then
         raise Program_Error;
      end if;
   end Verify;
end Support;
