with Duplicates; use Duplicates;
procedure Main is
   pragma SPARK_Mode (Off);  --  iterator on array
   X : Int_Array := (1, 0, 3, 5, 6, 3, 9, 0, 2);
   Y : Int_Array := (1, 0, 3, 5, 6, 9, 2);
   Z : Natural;
begin
   Dedupe (X, Z);
   pragma Assert (X(0 .. Z) = Y);
end Main;
