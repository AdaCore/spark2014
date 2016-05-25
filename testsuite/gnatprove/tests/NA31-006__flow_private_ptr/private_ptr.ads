package Private_Ptr with
  SPARK_Mode
is
   type V (C : Integer) is private;

private
   pragma SPARK_Mode (Off);

   type V (C : Integer) is record
      D : access Integer;
   end record;
end Private_Ptr;
