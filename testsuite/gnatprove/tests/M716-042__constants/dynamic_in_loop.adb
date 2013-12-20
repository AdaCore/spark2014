procedure Dynamic_In_Loop (Z : in out Positive) is
begin
   while Z < 10 loop
     declare
        C : constant Positive := Z;
        subtype T is Positive range 1 .. C;
        X : T := Z;
     begin
        pragma Loop_Invariant (X = Z and Z < 10);
        Z := Z + 1;
     end;
   end loop;
end Dynamic_In_Loop;
