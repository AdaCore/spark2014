procedure Dynamic_2D (Low1, Low2, High1, High2 : Integer) is
   type Dynamic_Matrix is array (Low1 .. High1, Low2 .. High2) of Character;

   procedure Flush (S : out Dynamic_Matrix) is
   begin
      for Col in S'Range (1) loop
         for Row in S'Range (2) loop
            S (Col, Row) := ' ';
         end loop;
      end loop;
   end;

   X : Dynamic_Matrix := (others => (others => 'o'));

begin
   Flush (X);
end;
