pragma SPARK_Mode;

procedure Repro (X : out Integer; B : Boolean) is
   pragma Warnings (".W");
   IS_DEBUG_BUILD : constant Integer := 1 with Warnings => Off;

   pragma Warnings (".W");
   function FUN_IS_DEBUG_BUILD return Integer is (1) with Static, Warnings => Off;

begin
   if B then
      if IS_DEBUG_BUILD /= 0 then
         X := 1;
      end if;
   else
      if FUN_IS_DEBUG_BUILD /= 0 then
         X := 2;
      end if;
   end if;
end;
