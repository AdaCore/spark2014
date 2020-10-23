with Ada.Unchecked_Deallocation;

procedure Test is
   type Int_Ptr is access Integer;

   procedure Free is new Ada.Unchecked_Deallocation (Object => Integer, Name => Int_Ptr);

   X : Int_Ptr := new Integer'(10);
   Y : Int_Ptr;
begin
   Y := X;
   Free (Y);
end Test;
