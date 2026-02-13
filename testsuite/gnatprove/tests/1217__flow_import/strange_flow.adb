procedure Strange_Flow with SPARK_Mode, Global => null is

   function B (X : aliased in out Integer) return not null access Integer with
     Import,
     Post => X = B'Result.all;

   V : aliased Integer := 1;
begin
   declare
      L : access Integer := B (V);
   begin
      L.all := 12;
   end;
end;
