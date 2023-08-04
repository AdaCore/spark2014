package body Pragma_Placement with SPARK_Mode is

   function F91 (X : Integer) return Integer is
      (if X <= 100 then F91 (F91 (X + 11)) else X - 10);
   procedure F91_Low (X : Integer) is null;
   procedure F91_High (X : Integer) is null;
   
   function Specialized_1
     (X : Integer;
      F : access function (X : Integer) return Integer) return Integer
   is
   begin
      return F (X);
   end Specialized_1;
   
   function Specialized_2
     (X : Integer;
      F : access function (X : Integer) return Integer) return Integer
   is
   begin
      return F (F (X));
   end Specialized_2;

end Pragma_Placement;
