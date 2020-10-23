with Ada.Unchecked_Deallocation;

procedure Test is
   type Int_Ptr is access Integer;
   type Int_Ptr_Ptr is access Int_Ptr;

   procedure Free is new Ada.Unchecked_Deallocation (Object => Int_Ptr, Name => Int_Ptr_Ptr);

   X : Int_Ptr     := new Integer'(10);  -- memory leak here
   Y : Int_Ptr     := new Integer'(11);
   Z : Int_Ptr_Ptr := new Int_Ptr'(Y);
begin
   Z.all := X;  -- memory leak here
   X := new Integer'(12);
   Free (Z);    -- memory leak here
end Test;
