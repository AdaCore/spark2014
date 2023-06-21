procedure P with Always_Terminates is
   procedure Neverend with Ghost, Pre => True is
   begin
      loop
         null;
      end loop;
   end;
begin
   Neverend;
end;
