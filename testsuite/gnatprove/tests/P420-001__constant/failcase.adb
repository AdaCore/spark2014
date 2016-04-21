procedure Failcase is

   type T is (A, B, C);

   State : T := T'First;

begin

   declare
      K : constant Natural :=
        (case State is
         when A => 1,
         when B => 2,
         when C => 3);
   begin
      null;
   end;

end Failcase;
