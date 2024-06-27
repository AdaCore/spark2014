package body Bad_Output with SPARK_Mode is
   procedure P (X : Child; Y : out E) is
   begin
      Y := -1;
   end P;
   procedure Fail_At_Runtime is
      X : Root'Class := Child'(null record);
      Y : E := 0;
   begin
      X.P (Y);
      pragma Assert (Y >= 0); --  ASSERTION_ERROR
   end Fail_At_Runtime;
end Bad_Output;
