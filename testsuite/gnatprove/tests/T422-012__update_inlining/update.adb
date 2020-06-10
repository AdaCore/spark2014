procedure Update with SPARK_Mode is
   type R is record
      A,B : Positive;
   end record;

   procedure Test (V : Integer) is
      X : R := (A|B => 1);
      Y : R := X'Update (A|B => V);
   begin
      null;
   end;

begin
   Test (0);
end;
