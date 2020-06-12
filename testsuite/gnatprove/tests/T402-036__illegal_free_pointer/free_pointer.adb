with Ada.Unchecked_Deallocation;

procedure Free_Pointer is
   type Int_Ptr is access Integer;
   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Ptr);
   X : Int_Ptr := new Integer'(3);
   Y : Int_Ptr := X;
begin
   Free (X);
end Free_Pointer;
