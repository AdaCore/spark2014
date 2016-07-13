package body All_Violations is

   Count : Integer := 0;

   function Increment return Integer is
   begin
      Count := Count + 1;
      return Count;
   end Increment;

   Last : Integer := 0;

   procedure Log (X : Integer) is
   begin
      Last := X;
   end Log;

   function Increment_And_Log (X : Integer) return Integer is
   begin
      Log (X);
      return X + 1;
   end Increment_And_Log;

   procedure Call_Increment_And_Log is
      X : Integer;
   begin
      X := Increment_And_Log (10);
   end Call_Increment_And_Log;

end All_Violations;
