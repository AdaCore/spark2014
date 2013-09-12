package body P is  

   procedure Incr_Threshold1 (X : in out Integer) is
   begin
      if X < Threshold then
         X := X + 1;
      end if;
   end Incr_Threshold1;

   procedure Incr_Threshold2 (X : in out Integer) is
   begin
      if X < Threshold then
         X := X + 1;
      end if;
   end Incr_Threshold2;

   procedure Incr_Threshold3 (X : in out Integer) is
   begin
      if X < Threshold then
         X := X + 1;
      end if;
   end Incr_Threshold3;

   procedure Incr_Threshold4 (X : in out Integer) is
   begin
      if X < Threshold then
         X := X + 1;
      end if;
   end Incr_Threshold4;

end P;
