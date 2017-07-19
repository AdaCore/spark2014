function Loop9_Bug return Boolean with SPARK_Mode is
begin
   for I in 1 .. 2 loop
      if I = 1 then
         return Bad : Boolean do
           Bad := False;
           for J in 1 .. I loop
              Bad := True;
           end loop;
         end return;
      end if;
   end loop;
   return True;
end Loop9_Bug;
