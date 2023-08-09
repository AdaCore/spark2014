procedure Main with SPARK_Mode is
begin
   loop
      declare
         pragma Loop_Invariant (False);
         function F return Boolean is (True);
         package P is
            function G return Boolean is (True);
            X : Boolean := False;
         end P;
      begin
         P.X := F;
      end;
   end loop;
end Main;
