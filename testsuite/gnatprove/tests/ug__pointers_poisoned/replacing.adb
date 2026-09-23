package body Replacing with SPARK_Mode is

   procedure Replace_In_View
     (A   : in out View_Array;
      I   : Positive;
      V   : Integer;
      Old : out Int_Acc) is
   begin
      Old := Take (A (I));
      --  A (I) is poisoned

      A (I) := Create_View (V);
      --  A (I) is readable again
   end Replace_In_View;

   procedure Replace
     (A   : aliased in out Acc_Array;
      I   : Positive;
      V   : Integer;
      Old : out Int_Acc)
   is
      A_View : constant not null access Readable_Array := Get_View (A);
   begin
      Replace_In_View (A_View.all, I, V, Old);
   end Replace;

end Replacing;
