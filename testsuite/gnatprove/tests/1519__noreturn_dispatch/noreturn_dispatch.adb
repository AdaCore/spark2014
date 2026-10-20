package body Noreturn_Dispatch with SPARK_Mode is
   procedure Stop (X : Root) is
      pragma Unreferenced (X);
   begin
      loop
         null;
      end loop;
   end Stop;

   overriding procedure Stop (X : Child) is
      pragma Unreferenced (X);
   begin
      loop
         null;
      end loop;
   end Stop;

   procedure Halt with Refined_Post => False is
   begin
      loop
         null;
      end loop;
   end Halt;
end Noreturn_Dispatch;
