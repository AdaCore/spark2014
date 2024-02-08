procedure Main with SPARK_Mode is
   type Cell;
   type Persistent_Tree is access constant Cell;
   type Cell is record
      Value : Integer;
      Left  : Persistent_Tree;
      Right : Persistent_Tree;
   end record;
   function Bad_Variant (X : Persistent_Tree) return Integer
     with Subprogram_Variant => (Structural => X);
   function Node (A : Integer; B : Persistent_Tree; C : Persistent_Tree)
                  return Persistent_Tree is
      (new Cell'(Value => A, Left => B, Right => C));
   function Bad_Variant (X : Persistent_Tree) return Integer is
   begin
      if X = null then
         return 0;
      end if;
      if X.Value = 0 then
         return Bad_Variant (X.Left);
      end if;
      if X.Left /= null and then X.Right /= null then

         --  Coverage corner-case: an access-typed expression in a structural
         --  variant which pass through marking/borrow-checking but is not
         --  recognized as a path expression.

         return Bad_Variant
           (declare
               Z : constant Persistent_Tree :=
                  Node (X.Value, X.Left.Left, X.Right.Right);
            begin
               Z);
      end if;
      return Bad_Variant (X.Right);
   end;
begin
   null;
end Main;
