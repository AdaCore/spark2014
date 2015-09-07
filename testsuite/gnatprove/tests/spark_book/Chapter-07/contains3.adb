with Ada.Strings.Fixed;
function Contains3 (S  : in String;
                    Ch : in Character) return Boolean
   with
      SPARK_Mode => On,
      Pre        => S'Length > 0,
      Post       => Contains3'Result = (for some I in S'Range => S (I) = Ch)
is
   Search_String : String (1 .. 1) := (others => Ch);
   Result_Index  : Natural;
begin
   -- An empty search string causes Index to raise Pattern_Error
   -- A starting point for the search that is out of bounds raises Index_Error
   pragma Assert (Search_String'Length > 0 and S'First in S'Range);
   Result_Index := Ada.Strings.Fixed.Index (Source  => S,
                                            Pattern => Search_String,
                                            From    => S'First);
   -- Index returns zero if it doesn't find the string or else it returns
   -- a position in the string where the pattern starts
   pragma Assume
     (if Result_Index  = 0 then
        (for all J in S'Range => S (J) /= Ch)
      else
        (Result_Index in S'Range and then S (Result_Index) = Ch));
   return Result_Index /= 0;
end Contains3;
