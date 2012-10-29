with Memory; use Memory;

procedure Test_Memory is
   type Arr is array (1 .. 10) of Chunk;
   Mems : Arr;
begin
   for J in 1 .. 10 loop
      Mems (J) := Alloc (1_000);
      pragma Assert (Mems (J) /= Null_Chunk);
   end loop;

   for J in reverse 2 .. 6 loop
      Free (Mems (J));
   end loop;

   Mems (1) := Alloc (5_000);
   pragma Assert (Mems (1) /= Null_Chunk);
end Test_Memory;
