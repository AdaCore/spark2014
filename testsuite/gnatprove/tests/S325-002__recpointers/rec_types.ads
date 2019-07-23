package Rec_Types with SPARK_Mode is
   package Test1 is
      type Tree_Node;
      type Tree is access Tree_Node;
      type Tree_Array is array (positive range <>) of Tree;
      type Tree_Array_Access is access Tree_Array;

      type Tree_Node is record
         Val  : Integer;
         Next : Tree_Array_Access;
      end record;

      procedure P_Tree;
   end Test1;

   package Test2 is
      type Tree_Node (D : Natural);
      type Tree is access Tree_Node;
      type Tree_Array is array (positive range <>) of Tree;

      type Tree_Node (D : Natural) is record
         Val  : Integer;
         Next : Tree_Array (1 .. D);
      end record;

      procedure P_Tree;
   end Test2;

   package Test3 is
      type Tree_2_Node;
      type Tree_2 is access Tree_2_Node;
      type Tree_3_Node;
      type Tree_3 is access Tree_3_Node;

      type Tree_2_Node is record
         Val  : Integer;
         Left, Right : Tree_3;
      end record;

      type Tree_3_Node is record
         Val  : Integer;
         Left, Middle, Right : Tree_2;
      end record;

      procedure P_Tree;
   end Test3;
end;
