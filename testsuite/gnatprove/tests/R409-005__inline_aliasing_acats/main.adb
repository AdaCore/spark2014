procedure Main is

   type T1 is record
      C : Integer;
   end record;

   type T2 is record
      C : T1;
   end record;

   type T3 is record
      C : T2;
   end record;

   A3 : T3 := (C => (C => (C => 0)));

   procedure P (X : in T1; Y : in out T1) is
   begin
      Y := X;
   end;

   A2 : T2 renames A3.C;
   A1 : T1 renames A2.C;

begin
   P (A1, A3.C.C);
end;
