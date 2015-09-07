with Ada.Strings.Fixed;
function Contains (S  : in String;
                   Ch : in Character) return Boolean
   with SPARK_Mode => On
is
   Search_String : String (1 .. 1) := (others => Ch);
   Result_Index  : Natural;
begin
   Result_Index := Ada.Strings.Fixed.Index (Source  => S,
                                            Pattern => Search_String,
                                            From    => S'First);
   return Result_Index /= 0;
end Contains;
