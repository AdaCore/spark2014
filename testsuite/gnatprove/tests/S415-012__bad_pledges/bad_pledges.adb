procedure Bad_Pledges with SPARK_Mode is
   function Bad1 (X : Integer; Y : Boolean) return Boolean is (True) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Bad1);
   procedure Bad2 (X : access constant Integer) is null with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Bad2);
   function Bad3 (X : access Integer) return access Integer is (X) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Bad3);
   function Bad4 (X : access constant Integer) return Integer is (1) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Bad4);
   function Bad5 (X : access constant Integer) return access constant Integer is (X);
   pragma Annotate (GNATprove, At_End_Borrow, Bad5);
   function Bad6 (X : access constant Integer) return access constant Integer with Ghost
   is
   begin
      return X;
   end Bad6;
   pragma Annotate (GNATprove, At_End_Borrow, Bad6);
   function Bad7 (X : access constant Integer) return access constant Integer is (null) with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, Bad7);
   function Bad8 (X : access constant Integer) return access constant Integer is (X) with Ghost,
     Pre => X /= null;
   pragma Annotate (GNATprove, At_End_Borrow, Bad8);
   function Bad9 (X : access constant Integer) return access constant Integer is (X) with Ghost,
     Post => Bad9'Result = X;
   pragma Annotate (GNATprove, At_End_Borrow, Bad9);
   function Bad10 (X : access constant Integer) return access constant Integer is (X) with Ghost,
     Contract_Cases =>
       (X = null => Bad10'Result = null,
        others   => Bad10'Result /= null);
   pragma Annotate (GNATprove, At_End_Borrow, Bad10);
   pragma Annotate (GNATprove, At_End_Borrow, "not an entity");
begin
   null;
end Bad_Pledges;
