with SPARK.Containers.Formal.Hashed_Maps;
with Ada.Containers; use Ada.Containers;
package Find_Map with SPARK_Mode is
   Max : constant Positive := 100;
   subtype Index is Positive range 1 .. Max;
   type Nat_Array is array (Index range <>) of Natural;

   function Hash (Id : Natural) return Hash_Type is (Hash_Type (Id));

   --  To help automatic prover, we should avoid using "=" directly for
   --  Equivalent_Keys and replace equality on elements by the wrapper
   --  in the program.
   function Equivalent_Keys (E1, E2 : Natural) return Boolean is (E1 = E2);

   package Index_Maps is new SPARK.Containers.Formal.Hashed_Maps
        (Key_Type        => Natural,
         Element_Type    => Index,
         Hash            => Hash,
         Equivalent_Keys => Equivalent_Keys);

   use Index_Maps;

   subtype Index_Map is Map (Count_Type (Max),
                             Default_Modulus (Count_Type (Max)));

   function Find_All (A : Nat_Array) return Index_Map with
     Post => (for all I in A'Range =>
                Contains (Find_All'Result, A (I)) and then
                Element (Find_All'Result, A (I)) in A'First .. I and then
                A (Element (Find_All'Result, A (I))) = A (I)) and
     (for all E in Natural =>
        (if Contains (Find_All'Result, E) then
             Element (Find_All'Result, E) in A'Range and then
             A (Element (Find_All'Result, E)) = E));

   function Find_Upto (A : Nat_Array; E : Natural; Last : Index)
                       return Natural with
     Pre  => Last in A'Range,
     Post => (if Find_Upto'Result = 0 then
                (for all I in A'First .. Last =>
                     A (I) /= E)
              else Find_Upto'Result in A'First .. Last and then
                 A (Find_Upto'Result) = E);
end;
