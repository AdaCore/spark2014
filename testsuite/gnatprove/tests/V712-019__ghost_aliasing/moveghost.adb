pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;
procedure Moveghost is
   type Ptr is access Integer;
   package P with Ghost is
      procedure Free is new Ada.Unchecked_Deallocation (Integer, Ptr);
   end P;
   use P;
   X : Ptr := new Integer'(42);
   Y : Ptr with Ghost;
begin
   Y := X;
   Free (Y);
end Moveghost;
