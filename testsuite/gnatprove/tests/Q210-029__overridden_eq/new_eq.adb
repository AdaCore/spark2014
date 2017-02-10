procedure New_Eq with SPARK_Mode is
   type My_Rec is record
      F : Integer;
      G : Integer;
   end record;
   function "=" (X, Y : My_Rec) return Boolean is (X.F = Y.F);

   X : My_Rec := (1, 2);
   Y : My_Rec := (1, 3);
begin
   pragma Assert (X /= Y);
end New_Eq;
