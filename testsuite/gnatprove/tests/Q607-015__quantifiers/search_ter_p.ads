with Types; use Types;

package Search_Ter_P with
     Spark_Mode is

   function Equal_Subrange
     (A : T_Arr;
      J : Integer;
      B : T_Arr) return Boolean
   is
     (A (J .. J - 1 + B'Length) = B)
   with
     Pre => A'Length >= B'Length and then A'Last < Positive'Last and then J in A'First .. A'Last + 1 - B'Length;

   function Has_Sub_Range_In_Prefix
     (A    : T_Arr;
      Last : Integer;
      B    : T_Arr) return Boolean
   is
     (for some J in A'First .. Last => Equal_Subrange (A, J, B))
   with
     Pre => A'Length >= B'Length and then A'Last < Positive'Last and then Last <= A'Last + 1 - B'Length,
     Ghost;

   function Has_Sub_Range
     (A : T_Arr;
      B : T_Arr) return Boolean is
     (Has_Sub_Range_In_Prefix (A, A'Last + 1 - B'Length, B)) with
      Pre => A'Length >= B'Length and then A'Last < Positive'Last,
      Ghost;

   function Search (A : T_Arr; B : T_Arr) return Option with
      Pre            => A'Last < Positive'Last and then B'First <= B'Last,
      Contract_Cases =>
      (B'Length = 0        => not Search'Result.Exists,
       A'Length < B'Length => not Search'Result.Exists,
       A'Length >= B'Length
       and then
       --  (for some J in A'First .. A'Last - B'Length + 1 =>
       --     A (J .. J - 1 + B'Length) = B) =>
       Has_Sub_Range(A, B) =>
         Search'Result.Exists
         and then Equal_Subrange (A, Search'Result.Value, B)
         and then
         (if
            Search'Result.Value > A'First
          then
            (not Has_Sub_Range_In_Prefix (A, Search'Result.Value - 1, B))),
       others => not Search'Result.Exists);

end Search_Ter_P;
