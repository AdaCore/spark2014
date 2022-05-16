procedure Main with SPARK_Mode is
   X : aliased Integer := 0;
   function Id (X : access Integer) return access Integer is (X);
begin
   for K in 1 .. 100 loop
      pragma Loop_Invariant (X = K - 1);
      declare
         X_Acc : constant access Integer := X'Access;
      begin
         X_Acc.all := X_Acc.all + 1;
      end;
   end loop;
   for K in 1 .. 100 loop
      pragma Loop_Invariant (X = K + 99);
      declare
         X_Acc : constant access Integer := X'Access;
         Y     : constant access Integer := Id (X_Acc);
      begin
         Y.all := Y.all + 1;
      end;
   end loop;
end Main;
