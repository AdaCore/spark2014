procedure Bad_Pledge_Calls_4 with SPARK_Mode is
   function Good (X : access constant Integer) return access constant Integer is (X) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Good);

   type Int_Access is access Integer;

   type Int_Arr is array (Positive range 1 .. 10) of Int_Access;

   A  : Int_Arr;
   I  : Positive := 1;
   X  : access Integer := A (I);
   pragma Assert (Good (X) = Good (A (I)));
begin
   null;
end Bad_Pledge_Calls_4;
