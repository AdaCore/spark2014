procedure Static_2D is
   type Static_Matrix is array (1 .. 10, 1 .. 10) of Character;

   procedure Flush (S : out Static_Matrix) is
   begin
      for Col in S'Range (1) loop
         for Row in S'Range (2) loop
            S (Col, Row) := ' ';
         end loop;
      end loop;
   end;

   X : Static_Matrix := (others => (others => 'o'));

begin
   Flush (X);
end;
