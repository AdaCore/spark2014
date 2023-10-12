procedure Main with SPARK_Mode is
   type A is access Integer;
   Y : A := new Integer'(0);
begin
   loop
      declare
         X : access Integer := Y;
         pragma Loop_Invariant (False);
      begin
         null;
      end;
   end loop;

end Main;
