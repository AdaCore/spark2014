package max_array_dimensions is

   subtype Index is Positive range 1 .. 10;

   type D1 is array (Index) of Integer;
   type D2 is array (Index, Index) of Integer;
   type D3 is array (Index, Index, Index) of Integer;
   type D4 is array (Index, Index, Index, Index) of Integer;
   type D5 is array (Index, Index, Index, Index, Index) of Integer;

end;
