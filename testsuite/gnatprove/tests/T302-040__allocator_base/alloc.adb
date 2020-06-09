with Types; use Types;

procedure Alloc is
   type Int_Ptr is access My_Integer;
   --  Access type

   X : Int_Ptr := new My_Integer'Base;
   --  Allocating the base subtype

   pragma Assert (X.all = -12345);
begin
   null;
end Alloc;
