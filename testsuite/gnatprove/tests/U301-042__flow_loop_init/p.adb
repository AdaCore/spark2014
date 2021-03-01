procedure P (Cond : Boolean) is
   procedure Set (Output : out Integer) is null;

   type T1 is record
      A : Integer;
      B : Integer;
   end record;

   type A1 is array (Boolean) of T1;

   type T2 is record
      C2 : A1;
   end record;

   type A2 is array (Boolean) of T2;

   type T3 is record
      C3 : A2;
   end record;

   C4 : T3;

begin
   for J2 in Boolean'Range loop
      if Cond then
         C4.C3 (J2) := (C2 => (others => T1'(A => 0, B => 0)));
      else
         for J1 in Boolean'Range loop
            Set (C4.C3 (J2).C2 (J1).A);
         end loop;
      end if;
   end loop;
end;
