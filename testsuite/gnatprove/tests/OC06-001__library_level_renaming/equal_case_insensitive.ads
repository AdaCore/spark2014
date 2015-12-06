with Ada.Strings.Equal_Case_Insensitive;

function Equal_Case_Insensitive
  (Left, Right : String)
  return Boolean renames Ada.Strings.Equal_Case_Insensitive;

pragma Pure (Equal_Case_Insensitive);
