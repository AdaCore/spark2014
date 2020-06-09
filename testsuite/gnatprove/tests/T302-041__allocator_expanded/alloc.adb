with Types;

procedure Alloc is
   X : Types.Int_Ptr := new Types.My_Integer;
   --  Allocating the base subtype

   use type Types.My_Integer;
   pragma Assert (X.all = -12345);
begin
   null;
end Alloc;
