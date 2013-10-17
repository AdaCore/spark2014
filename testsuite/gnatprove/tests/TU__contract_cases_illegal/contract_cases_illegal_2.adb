package body Contract_Cases_Illegal_2
  with SPARK_Mode
is
   procedure Overlapping_Conditions (A, B : Integer ; C : out Integer) is
   begin
      C := Integer'Min (A, B);
   end Overlapping_Conditions;

   procedure Incorrect_Contract (A, B : Integer ; C : out Integer) is
   begin
      C := Integer'Min (A, B);
   end Incorrect_Contract;
end Contract_Cases_Illegal_2;
