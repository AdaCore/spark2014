procedure Repro with SPARK_Mode is

   function Bor (X : not null access Integer) return not null access Integer
   is (X);

   V : aliased Integer := 0;
begin
   declare
      B : constant not null access Integer := Bor (V'Access);
   begin
      B.all := 1;
   end;
end Repro;
