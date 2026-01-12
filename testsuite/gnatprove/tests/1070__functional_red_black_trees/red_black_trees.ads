pragma Ada_2022;

with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Trees;

package Red_Black_Trees with SPARK_Mode is
   type Left_Or_Right is (Left, Right);
   type Red_Or_Black is (Red, Black);
   type Value_And_Color is record
      V : Integer;
      C : Red_Or_Black;
   end record;
   package Binary_Trees is new SPARK.Containers.Functional.Trees
     (Left_Or_Right, Value_And_Color, Use_Logical_equality => True);
   use Binary_Trees;
   package Int_Sets is new SPARK.Containers.Functional.Sets (Integer);
   use Int_Sets;

   function Opt_Add (S : Int_Sets.Set; V : Integer) return Int_Sets.Set is
     (if Contains (S, V) then S else Add (S, V));

   function Model (T : Tree) return Int_Sets.Set is
     (if Is_Empty (T) then Empty_Set
      else Opt_Add (Union (Model (Child (T, Left)), Model (Child (T, Right))), Get (T).V))
     with Ghost,
     Subprogram_Variant => (Decreases => (Height (T)));

   function Nb_Blacks (T : Tree) return Big_Natural is
     (if Is_Empty (T) then 0
      else Nb_Blacks (Child (T, Left)) + Big_Natural'(if Get (T).C = Black then 1 else 0))
     with Subprogram_Variant => (Decreases => Height (T)), Ghost;

   function Is_Balanced (T : Tree) return Boolean is
     (Is_Empty (T)
      or else
        ((if Get (T).C = Red
         then (Is_Empty (Child (T, Left)) or else Get (Child (T, Left)).C = Black)
         and (Is_Empty (Child (T, Right)) or else Get (Child (T, Right)).C = Black))
         and then Nb_Blacks (Child (T, Left)) = Nb_Blacks (Child (T, Right))
         and then Is_Balanced (Child (T, Left))
         and then Is_Balanced (Child (T, Right))))
     with Subprogram_Variant => (Decreases => Height (T)), Ghost;

   function Is_Search_Tree (T : Tree) return Boolean is
     (Is_Empty (T)
      or else
        ((for all V of Model (Child (T, Right)) => Get (T).V < V)
         and then (for all V of Model (Child (T, Left)) => Get (T).V > V)
         and then Is_Search_Tree (Child (T, Left))
         and then Is_Search_Tree (Child (T, Right))))
     with Subprogram_Variant => (Decreases => Height (T)), Ghost;

   function Contains (T : Tree; V : Integer) return Boolean with
     Pre => Is_Search_Tree (T),
     Post => Contains'Result = Contains (Model (T), V);

   procedure Insert (T : in out Tree; V : Integer) with
     Pre => Is_Search_Tree (T)
     and then (Is_Empty (T) or else Get (T).C = Black)
     and then Is_Balanced (T),
     Post => Is_Search_Tree (T)
     and then (Is_Empty (T) or else Get (T).C = Black)
     and then Is_Balanced (T)
     and then Contains (Model (T), V)
     and then Included_Except (Model (T), Model (T'Old), V)
     and then Model (T'Old) <= Model (T);
end Red_Black_Trees;
