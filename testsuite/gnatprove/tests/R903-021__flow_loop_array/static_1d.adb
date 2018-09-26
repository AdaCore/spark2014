procedure Static_1D is
   type Static_String is array (1 .. 10) of Character;

   procedure Flush (S : out Static_String) is
   begin
      for C in S'Range loop
         S (C) := ' ';
      end loop;
   end;

   X : Static_String := "ABCDEFGHIJ";

begin
   Flush (X);
end;
