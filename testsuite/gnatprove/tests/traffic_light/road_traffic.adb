package body Road_Traffic
  with SPARK_Mode
is

   procedure To_Green (L : in out Lights_Type; P : Path) is
   begin
      L (P) := Green;
   end To_Green;

   procedure To_Yellow (L : in out Lights_Type; P : Path) is
   begin
      L (P) := Yellow;
   end To_Yellow;

   procedure To_Red (L : in out Lights_Type; P : Path) is
   begin
      L (P) := Red;
   end To_Red;

end Road_Traffic;
