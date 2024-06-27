package body Bad_Input with SPARK_Mode is
   procedure P (R : Child; X : E; Target : out Integer) is
   begin
      Target := 0;
   end P;

   procedure P (R : GrandChild; X : E; Target : out Integer) is
   begin
      Target := Integer (X);
   end P;

   procedure Fail_At_Runtime is
      X : E := -1;
      Y : Child'Class := GrandChild'(null record);
      Z : Integer;
   begin
      Y.P (X, Z); --  INVARIANT_CHECK:FAIL
   end Fail_At_Runtime;
end Bad_Input;
