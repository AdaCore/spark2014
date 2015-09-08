with Generic_Searchers;

procedure Prime_Search(Search_Item : in Natural; Prime_Index : out Natural)
  with SPARK_Mode => On
is
   subtype Index_Type is Positive range 1 .. 10;
   type Natural_Array_Type is array(Index_Type) of Natural;

   Primes : constant Natural_Array_Type :=
     (2, 3, 5, 7, 11, 13, 17, 19, 23, 29);

   Found    : Boolean;
   Position : Positive;

   procedure Natural_Search is new Generic_Searchers.Binary_Search
     (Element_Type => Natural,
      Index_Type   => Index_Type,
      Array_Type   => Natural_Array_Type);
begin
   pragma Assert(for all I in Primes'Range =>
                   (for all J in I + 1 .. Primes'Last => Primes(I) < Primes(J)));
   Natural_Search(Search_Item, Primes, Found, Position);
   if Found then
      Prime_Index := Position;
   else
      Prime_Index := 0;  -- Zero indicates "not found."
   end if;
end Prime_Search;
