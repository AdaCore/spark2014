procedure Sub (X : in out Integer) with
  SPARK_Mode
is
   procedure Doit (X : out Integer) is
   begin
      if True then
         X := 1;
         return;
      else
         X := 0;
         return;
      end if;
   end Doit;
begin
   Doit (X);
end Sub;
