package Types with
  SPARK_Mode
is
   type T (D : Integer) is private with Default_Initial_Condition => Valid (T);
   function Valid (X : T) return Boolean is (True);
private
--   pragma SPARK_Mode (Off);
   type T (D : Integer) is tagged record
      C : Integer;
   end record;
end Types;
