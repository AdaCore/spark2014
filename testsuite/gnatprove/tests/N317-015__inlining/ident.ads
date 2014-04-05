package Ident
  with SPARK_Mode
is
   function Id_Public (X : Integer) return Integer;
   procedure Incr_Public (X : in Positive; Y : out Natural);
   procedure Test;
private
   function Id_Private (X : Integer) return Integer;
   procedure Incr_Private (X : in Positive; Y : out Natural);
end Ident;
