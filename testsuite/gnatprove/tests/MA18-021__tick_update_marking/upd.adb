procedure Upd is
   type R1 is record
      X, Y : Integer;
   end record;
   type R2 is record
      U, V : R1;
   end record;
   X : R2;
begin
   X := X'Update (U => (X => 1, Y => 2));
end Upd;
