procedure Iter_Multi_Array is
   type Ar is array (1 .. 10, -1 .. 1) of Natural;
   X : Ar := (others => (others => 0));
begin
   pragma Assert (for all J1 in X'Range(1) => (for all J2 in X'Range(2) => X(J1,J2) = 0));
   pragma Assert (for all E of X => E = 0);

   for E of X loop
      E := 1;
   end loop;
   pragma Assert (for all E of X => E = 1);

   for J1 in X'Range(1) loop
      for J2 in X'Range(2) loop
         declare
            E : Natural renames X(J1,J2);
         begin
            E := 2;
         end;
         pragma Loop_Invariant
           (for all K1 in 1 .. J1 - 1 =>
              (for all K2 in X'Range(2) => X(K1,K2) = 2));
         pragma Loop_Invariant
           (for all K2 in -1 .. J2 => X(J1,K2) = 2);
      end loop;
      pragma Loop_Invariant
        (for all K1 in 1 .. J1 =>
           (for all K2 in X'Range(2) => X(K1,K2) = 2));
   end loop;
   pragma Assert (for all E of X => E = 2);

end Iter_Multi_Array;
