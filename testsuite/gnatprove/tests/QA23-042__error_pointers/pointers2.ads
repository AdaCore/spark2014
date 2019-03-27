package Pointers2 with
  SPARK_Mode
is
   type Int_Ptr is access Integer;

   procedure Bad_Swap (X, Y : in out Int_Ptr);

   procedure Swap (X, Y : in out Int_Ptr);

   X, Y : Int_Ptr;

   procedure Bad_Swap_Global with
     Global => (In_Out => (X, Y));

   procedure Swap_Global with
     Global => (In_Out => (X, Y));
   
   procedure Bad_Borrow (X, Y : in out Int_Ptr);
   
   procedure Bad_Move (X, Y : in out Int_Ptr);
   
end Pointers2;

