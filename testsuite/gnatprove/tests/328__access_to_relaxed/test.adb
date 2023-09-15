procedure Test with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;

   type RR is new R with Relaxed_Initialization;

   type RR_Access is access RR;

   package Nested is
      type Root_1 is tagged record
         F : RR;
      end record;

      type Root_2 is tagged record
         F : RR_Access;
      end record;
   end Nested;
begin
   null;
end Test;
