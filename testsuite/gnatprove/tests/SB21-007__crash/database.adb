with SPARK.Containers.Formal.Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package body Database with SPARK_Mode
is

   package Big_From_Count is new Signed_Conversions
     (Int => Count_Type);

   function Big (C : Count_Type) return Big_Integer renames
     Big_From_Count.To_Big_Integer;

   package DB_Pack is new SPARK.Containers.Formal.Doubly_Linked_Lists
     (Element_Type => DB_Entry_Type,
      "="          => "=");
   use DB_Pack;

   Database : DB_Pack.List (1000);
   DB_Model : Model_Type with Ghost;

   --------------
   -- Contains --
   --------------

   function Contains
     (Email : Email_Address_Type;
      Key   : Integer) return Boolean
   is (Contains (Database, (Key, Email)));

   ---------------
   -- Invariant --
   ---------------

   function Invariant return Boolean is

      --  Database does not contain duplicates

     ((for all I in Formal_Model.Model (Database) =>
         (for all J in Formal_Model.Model (Database) =>
              (if Formal_Model.Element (Formal_Model.Model (Database), I) =
                   Formal_Model.Element (Formal_Model.Model (Database), J)
               then I = J)))

      --  Database and DB_Model contain the same pairs

      and (for all Pair of Database => Contains (DB_Model, Pair))
      and (for all Pair of DB_Model => Contains (Database, Pair))
      and Length (DB_Model) = Big (Length (Database)))
   with SPARK_Mode => Off; -- due to call to allocating function

end Database;
