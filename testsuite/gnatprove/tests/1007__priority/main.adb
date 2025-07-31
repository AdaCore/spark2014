procedure Main (I : Integer) with SPARK_Mode is
   pragma Priority (4);
begin
   case I is
      when others =>
         null;
   end case;
end Main;
