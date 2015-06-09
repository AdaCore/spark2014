procedure Iter_Array is
   type Ar is array (1 .. 10) of Natural;
   X : Ar := (others => 0);
begin
   pragma Assert (for all J in X'Range => X(J) = 0);
   pragma Assert (for all E of X => E = 0);

   for E of X loop
      E := 1;
   end loop;
   pragma Assert (for all E of X => E = 1);

   for J in X'Range loop
      declare
         E : Natural renames X(J);
      begin
         E := 2;
      end;
      pragma Loop_Invariant (for all K in 1 .. J => X(K) = 2);
   end loop;
   pragma Assert (for all E of X => E = 2);

end Iter_Array;
