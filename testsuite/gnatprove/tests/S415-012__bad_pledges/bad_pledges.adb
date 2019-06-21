procedure Bad_Pledges with SPARK_Mode is
   function Bad1 (X : Integer) return Boolean is (True) with Ghost;
   pragma Annotate (GNATprove, Pledge, Bad1);
   function Bad2 (X : Integer; Y : Boolean) return Boolean is (Y) with Ghost;
   pragma Annotate (GNATprove, Pledge, Bad2);
   function Bad3 (X : access Integer; Y : Integer) return Boolean is (True) with Ghost;
   pragma Annotate (GNATprove, Pledge, Bad3);
   function Bad4 (X : access Integer; Y : Boolean) return Integer is (1) with Ghost;
   pragma Annotate (GNATprove, Pledge, Bad4);
   function Bad5 (X : access Integer; Y : Boolean) return Boolean is (Y);
   pragma Annotate (GNATprove, Pledge, Bad5);
   function Bad6 (X : access Integer; Y : Boolean) return Boolean with Ghost
   is
   begin
      return Y;
   end Bad6;
   pragma Annotate (GNATprove, Pledge, Bad6);
   function Bad7 (X : access Integer; Y : Boolean) return Boolean is (True) with Ghost;
   pragma Annotate (GNATprove, Pledge, Bad7);
begin
   null;
end Bad_Pledges;
