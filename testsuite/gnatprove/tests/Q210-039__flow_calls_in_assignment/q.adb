with P;
procedure Q with Annotate => (GNATprove, Terminating) is
   type T is array (Integer) of Positive;

   A : T := (others => 1);

begin
   A (P.Fun) := 3;
end;
