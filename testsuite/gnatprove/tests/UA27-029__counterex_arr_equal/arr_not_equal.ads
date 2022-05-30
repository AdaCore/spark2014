package Arr_Not_Equal is

   type Arr is array (Integer range <>) of Integer;

   function Empty (A : Arr) return Boolean;

   function All_Same_Values (A : Arr) return Boolean
      with Pre => A'Length = 3;

   function All_Same_Others (A : Arr) return Boolean
      with Pre => A'Length = 3;

   function All_Diff_Values (A : Arr) return Boolean
      with Pre => A'Length = 3;

   function All_Diff_Others (A : Arr) return Boolean
      with Pre => A'Length = 3;

   function Mix (A : Arr) return Boolean
      with Pre => A'Length = 11;

end Arr_Not_Equal;
