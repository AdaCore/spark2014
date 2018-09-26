procedure Dynamic_1D (Low, High : Integer) is
   type Dynamic_String is array (Low .. High) of Character;

   procedure Flush (S : out Dynamic_String) is
   begin
      for C in S'Range loop
         S (C) := ' ';
      end loop;
   end;

   X : Dynamic_String := (others => 'o');

begin
   Flush (X);
end;
