function Sliced_Prefix (J, K : Integer) return Boolean
   with Pre => J in 1 .. 3 and K in 1 .. 3,
        Depends => (Sliced_Prefix'Result => (J, K))
is
   type Aligned_String is array (Positive range <>) of aliased Character;
   X : constant Aligned_String (1 .. 3) := "abc";
   Y : constant Aligned_String (1 .. 1) with Import, Address => X (J .. J)'Address;
   Z : constant Aligned_String (1 .. 1) with Import, Address => X (K .. K)'Address;
begin
   return Y (1) = Z (1);
end;
