package body A with SPARK_Mode is
   procedure P (Param : in T) is
   begin
      if Param.all > 0 then
         Param.all := 0;
      end if;
   end P;
end A;
