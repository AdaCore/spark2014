procedure Test_Annotate (I : Integer) with SPARK_Mode is
begin
   if False then
      if I = 0 then
         raise Program_Error;
         pragma Annotate (GNATprove, Intentional, "toto", "it was on purpose");
      elsif I = 15 then
         raise Program_Error;
         pragma Annotate (GNATprove, Intentional, "toto", "it was on purpose");
      else
         raise Program_Error;
         pragma Annotate (GNATprove, Intentional, "toto", "it was on purpose");
      end if;
   else
      if I = 0 then
         null;
      elsif False then
         raise Program_Error;
         pragma Annotate (GNATprove, Intentional, "toto", "it was on purpose");
      elsif True then
         null;
      else
         raise Program_Error;
         pragma Annotate (GNATprove, Intentional, "toto", "it was on purpose");
      end if;
   end if;
end Test_Annotate;
