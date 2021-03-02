procedure P (Cond : Boolean) is
   procedure Set (Output : out Integer) is null;

   type R is record
      C : Integer;
   end record;

   type A is array (Boolean) of R;

   X : A;

begin
   for J in Boolean'Range loop
      if Cond then
         X (J) := (C => 0);
      else
         Set (X (J).C);
      end if;
   end loop;
end;
