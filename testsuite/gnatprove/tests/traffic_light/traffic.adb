package body Traffic
  with SPARK_Mode
is

   procedure To_Green (L : in out Lights_Type; P : Path) is
   begin
      L (P) := Green;
   end To_Green;

   procedure To_Amber (L : in out Lights_Type; P : Path) is
   begin
      L (P) := Amber;
   end To_Amber;

   procedure To_Red (L : in out Lights_Type; P : Path) is
   begin
      L (P) := Red;
   end To_Red;

end Traffic;
