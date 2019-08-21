procedure Bad_Pledge_Calls with SPARK_Mode is
   function Good (X : access Integer; Y : Boolean) return Boolean is (Y) with Ghost;
   pragma Annotate (GNATprove, Pledge, Good);

   type Int_Access is access Integer;

   type Holder is record
      R : Int_Access;
   end record;

   X         : Holder;
   Bad_Call1 : Boolean := Good (X.R, True) with Ghost;

   Y         : Int_Access;
   Bad_Call2 : Boolean := Good (Y, True) with Ghost;

   Z         : access Integer := Y;
   Good_Call : Boolean := Good (Z, True) with Ghost;
begin
   null;
end Bad_Pledge_Calls;
