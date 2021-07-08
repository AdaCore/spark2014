procedure Pointer_Eq with SPARK_Mode is
   type Int_Acc is access Integer;
   type Rec is record
      C : Int_Acc;
   end record;

   X, Y : Rec := (C => new Integer'(15));
begin
   pragma Assert (X = Y);  -- Should not be proved.
end Pointer_Eq;
