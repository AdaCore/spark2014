with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

function Replace_Prefix (String_With_Prefix : String; Prefix, New_Prefix : String) return String
     with
       Pre =>
   -- Length constraints (added to help Prover)
     String_With_Prefix'Length >= Prefix'Length and then
   -- Empty string cannot be [Postive'Last + 1 .. Positive'Last] due to overflow hence
     To_Big_Integer(String_With_Prefix'First) + To_Big_Integer(Prefix'Length) <= To_Big_Integer(Positive'Last) and then
     To_Big_Integer(New_Prefix'First) + To_Big_Integer(New_Prefix'Length) <= To_Big_Integer(Positive'Last) and then
     -- Overflow protection, since the length of a string is limited by the range of Natural
     -- [0 .. Natural'Last]
     -- Furthermore, New_Prefix'First >= 1, so not whole range is necessarily available
     -- [type String is array (Positive range <>) of Character + with exceptions for empty string]
     To_Big_Integer(String_With_Prefix'Length) - To_Big_Integer(Prefix'Length) <=
     To_Big_Integer(Positive'Last) - To_Big_Integer(New_Prefix'Last) and then
     -- Value constraints
     String_With_Prefix (String_With_Prefix'First .. String_With_Prefix'First + (Prefix'Length - 1)) = Prefix,
     Post =>
   -- Length constraints (added to help Prover)
     To_Big_Integer(Replace_Prefix'Result'Length) - To_Big_Integer(New_Prefix'Length) =
     To_Big_Integer(String_With_Prefix'Length) - To_Big_Integer(Prefix'Length) and
     -- Value Constraints
     Replace_Prefix'Result (Replace_Prefix'Result'First .. Replace_Prefix'Result'First + (New_Prefix'Length - 1)) = New_Prefix and
     Replace_Prefix'Result (Replace_Prefix'Result'First + New_Prefix'Length .. Replace_Prefix'Result'Last) = String_With_Prefix (String_With_Prefix'First + Prefix'Length .. String_With_Prefix'Last),
      Global => null;

   -- Replace 'Prefix' with 'New_Prefix' in 'String_With_Prefix'.
   -- @param String_With_Prefix String that starts with Prefix
   -- @param Prefix Prefix present in String_With_Prefix to be replaced by New_Prefix
   -- @param New_Prefix New Prefix to replace Prefix in String_With_Prefix
   -- @return Given that String_With_Prefix = Prefix & Remainder return is equal to New_Prefix & Remainder
