procedure Bad_Pledge_Calls_3 with SPARK_Mode is
   function Good (X : access constant Integer) return access constant Integer is (X) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Good);

   type Int_Access is access Integer;

   type Holder is record
      R : Int_Access;
   end record;

   X  : Holder;
   pragma Assert (X.R = Good (X.R));
begin
   null;
end Bad_Pledge_Calls_3;
