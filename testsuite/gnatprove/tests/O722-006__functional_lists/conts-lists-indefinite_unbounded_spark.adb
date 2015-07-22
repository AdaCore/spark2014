package body Conts.Lists.Indefinite_Unbounded_SPARK with SPARK_Mode => Off is

   ----------
   -- Copy --
   ----------

   function Copy (Self : List'Class) return List'Class is
   begin
      return Result : List do
         Result.Assign (Self);
      end return;
   end Copy;

end Conts.Lists.Indefinite_Unbounded_SPARK;
