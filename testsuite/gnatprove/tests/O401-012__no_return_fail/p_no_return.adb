package body p_no_return with SPARK_Mode is
   procedure Returning is
   begin
      null;
   end Returning;

   function Id (C : Natural) return Natural is (C);

   procedure Difficult_Non_Returning (C : Natural) is
      Current : Natural := C;
   begin
      while Current <= C loop
         Current := Id (Current);
      end loop;
   end Difficult_Non_Returning;
end p_no_return;
