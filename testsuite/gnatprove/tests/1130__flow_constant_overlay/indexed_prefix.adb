function Indexed_Prefix (J : Integer) return Character
   with Pre => J in 1 .. 3,
               Depends => (Indexed_Prefix'Result => J)
is
   type Aligned_String is array (1 .. 3) of aliased Character;
   X : constant Aligned_String := "abc";
   Y : constant Character with Import, Address => X (J)'Address;
begin
   return Y;
end;
