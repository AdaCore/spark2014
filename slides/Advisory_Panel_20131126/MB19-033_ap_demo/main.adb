with Binary_Search;

procedure main
is
   My_Array : Binary_Search.Ar := (others => 0);
   My_Index : Binary_Search.T;

   function where_are_the_errors (Input : Integer) return Integer
   is
      x, y, k : integer;
   begin
      k := input / 100;
      x := 2;
      y := k + 5;

      while x < 10 loop
         x := x + 1;
         y := y + 3;
      end loop;

      if 3*k + 100 > 43 then
         y := y + 1;
         x := x / (x - y);
      end if;

      return x;

   end where_are_the_errors;

begin

   My_Index := Binary_Search.Search (My_Array, 1);

end main;
