with SPARK.Containers.Functional.Sets;

package Hashtbl
  with SPARK_Mode
is

   type U32 is mod 2 ** 32;

   type Data is new U32;

   type Cell_Rec;

   type Cell is access Cell_Rec;

   type Cell_Rec is record
      D    : Data;
      Next : Cell;
   end record;

   function Hash (X : Data; M : U32) return U32
   is (U32 (X) mod M)
   with Pre => M > 0;

   function Has_Hash (C : access constant Cell_Rec; H, M : U32) return Boolean
   is (if C = null
       then True
       else Hash (C.D, M) = H and then Has_Hash (C.Next, H, M))
   with
     Pre => M > 0,
     Subprogram_Variant => (Structural => C);

   type Cell_Arr is array (U32 range <>) of Cell
   with
     Predicate =>
       Cell_Arr'First = 0
       and then Cell_Arr'Length in 1 .. U32'Last
       and then
         (for all H in Cell_Arr'Range =>
            Has_Hash (Cell_Arr (H), H, U32 (Cell_Arr'Length)));

   type Cell_Arr_Ptr is not null access Cell_Arr;

   type Table is record
      Cells : Cell_Arr_Ptr;
      Size  : Natural;
   end record;

   package M
     with Ghost
   is

      package FS is new SPARK.Containers.Functional.Sets (Data);

      function Add_Permissive (S : FS.Set; X : Data) return FS.Set
      is (if FS.Contains (S, X) then S else FS.Add (S, X));

      function Model (C : access constant Cell_Rec) return FS.Set
      is (if C /= null
          then Add_Permissive (Model (C.Next), C.D)
          else FS.Empty_Set)
      with Subprogram_Variant => (Structural => C);

      function Model (C : Cell_Arr) return FS.Set
      is (if C'Length = 0
          then FS.Empty_Set
          elsif C'Length = 1
          then Model (C (C'First))
          else
            FS.Union (Model (C (C'Last)), Model (C (C'First .. C'Last - 1))))
      with Subprogram_Variant => (Decreases => C'Length);

      function Model (T : Table) return FS.Set
      is (Model (T.Cells.all));
   end M;

   function Mem (T : Table; Key : Data) return Boolean
   with
     Pre  => T.Size < Natural'Last,
     Post =>
       (Mem'Result =
          M.FS.Contains
            (M.Model (T.Cells (Hash (Key, U32 (T.Cells'Length)))), Key));

   procedure Insert (T : in out Table; Key : Data; Success : out Boolean)
   with
     Pre  => T.Size < Natural'Last,
     Post =>
       M.FS.Contains
         (M.Model (T.Cells (Hash (Key, U32 (T.Cells'Length)))), Key);
   --  Success is false if the key was already in the map

end Hashtbl;
