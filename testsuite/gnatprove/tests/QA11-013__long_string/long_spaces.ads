package long_spaces is

   --Ugh. But what can you do?
   Spaces32   : constant String := "                                ";
   Spaces64   : constant String := Spaces32  & Spaces32;
   Spaces128  : constant String := Spaces64  & Spaces64;
   Spaces256  : constant String := Spaces128 & Spaces128;
   Spaces512  : constant String := Spaces256 & Spaces256;
   Spaces1024 : constant String := Spaces512 & Spaces512;

   --1161 spaces, see above
   BlankKey   : constant String := Spaces1024 &
                                   Spaces128 & "         ";

end;
