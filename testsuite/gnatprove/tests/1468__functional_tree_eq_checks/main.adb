with SPARK.Containers.Functional.Trees;

procedure Main with SPARK_Mode is

   type LR is (Left, Right);

   package T is new SPARK.Containers.Functional.Trees
     (LR, Float, Use_Logical_Equality => True);
   --  We instanciate functional trees with Use_Logical_Equality => True while
   --  supplying an equality (predefined "=" on floats) that is not the
   --  logical equality. There should be a failed parameter check.

   --  To demonstrate the issue, we prove False using operations of T.

   use T;

   function Sign_Root (X : Tree) return Boolean is
     (Float'Copy_Sign (1.0, Get (X)) > 0.0) with
     Pre => not Is_Empty (X);

   X : Tree := Create (+0.0);
   Y : Tree := Create (-0.0);

begin
   --  X = Y is true as it uses "=" on floats.
   pragma Assert (X = Y);

   --  "=" on trees is wrongly interpreted as logical equality because
   --  Use_Logical_Equality is set, so it is congruent.
   pragma Assert (Sign_Root (X) = Sign_Root (Y));

   --  We are unsound here.
   pragma Assert (False);
end Main;
