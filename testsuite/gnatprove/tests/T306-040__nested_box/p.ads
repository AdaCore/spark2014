package P is

   type T1 (D1 : Boolean := False) is record
      C1 : Boolean := True;
   end record;

   type T2 is record
      C2 : T1;
   end record;

   X2 : T2 := (others => <>);

end;
