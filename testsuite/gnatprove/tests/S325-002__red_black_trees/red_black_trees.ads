package Red_Black_Trees with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Red_Or_Black is (Red, Black);

   type Tree_Cell;

   type Tree is access Tree_Cell;

   type Tree_Cell is record
      Value : Integer;
      Color : Red_Or_Black;
      Left  : Tree;
      Right : Tree;
   end record;

   procedure Insert (T : in out Tree; V : Integer);

end Red_Black_Trees;
