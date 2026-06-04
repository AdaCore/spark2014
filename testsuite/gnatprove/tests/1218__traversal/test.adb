procedure Test with SPARK_Mode is
   type R is record
      F, G : aliased Integer;
   end record;

   G : Integer := 12;

   function B (X : aliased in out Integer) return not null access Integer with Import, Global => G;

   function B2 (X : aliased in out R) return not null access Integer is (B (X.F));

   X : aliased R := (1, 2);
begin
   declare
      Y : access Integer := B2 (X);
   begin
      Y.all := 12;
   end;
   pragma Assert (X.G = 2);
end;
