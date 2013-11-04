package body Q
  with SPARK_Mode
is
   procedure Init1 (KS : out IA) is
      pragma Warnings (Off, KS);
   begin
      for I in IDX loop
         KS (I) := 0;
      end loop;
   end Init1;

   procedure Init2 (KS : out IA) is
   begin
      pragma Warnings (Off, KS);
      for I in IDX loop
         KS (I) := 0;
      end loop;
   end Init2;

   procedure Increase_Glob
     with Global  => (In_Out => Glob),
          Depends => (Glob => Glob)
   is
      pragma Warnings (Off, Glob);
   begin
      Glob := 2;
   end Increase_Glob;
end Q;
