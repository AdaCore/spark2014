procedure Unexpected with SPARK_Mode is
   function "&" (Left, Right : Boolean) return Boolean with
     Side_Effects,
     Global => null;

   ---------
   -- "&" --
   ---------

   function "&" (Left, Right : Boolean) return Boolean is
   begin
      if Left then
         raise Program_Error; --@RAISE:FAIL
      end if;
      return Right;
   end "&";
begin
   null;
end Unexpected;
