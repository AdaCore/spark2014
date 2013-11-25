with Binary_Search;

procedure main
is
   My_Array : Binary_Search.Ar := (1, 2, 3, 3, 5, others => 10);
   My_Index : Binary_Search.T;

begin

   My_Index := Binary_Search.Search (My_Array, 4);

end main;
