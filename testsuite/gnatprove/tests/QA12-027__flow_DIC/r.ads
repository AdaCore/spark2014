package R is
   type TTT is private with Default_Initial_Condition;
private
   pragma SPARK_Mode (Off);
   type TTT is record
      A : Integer;
   end record;
end R;
