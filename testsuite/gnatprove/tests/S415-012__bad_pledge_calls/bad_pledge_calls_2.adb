procedure Bad_Pledge_Calls_2 with SPARK_Mode is
   function Good (X : access constant Integer) return access constant Integer is (X) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Good);

   type Int_Access is access Integer;

   type Holder is record
      R : Int_Access;
   end record;

   Y : Int_Access;
   pragma Assert (if Y /= null then Y.all = Good (Y).all);
begin
   null;
end Bad_Pledge_Calls_2;
