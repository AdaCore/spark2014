package Ext is
   type Root is tagged record
      F : Integer;
   end record;
   function Get (X : Root) return Integer is (X.F);
   type Child is new Root with record
      G : Integer;
   end record;
   function Get (X : Child) return Integer is (X.G) with SPARK_Mode => Off;
   type Grand_Child is new Child with record
      H : Integer;
   end record;
   function Get (X : Grand_Child) return Integer is (X.H);
end Ext;
