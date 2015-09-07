private with Ada.Finalization;
package Interval_Trees
   with SPARK_Mode => On
is
   type Interval is
      record
         Low  : Float;
         High : Float;
      end record;

   type Tree is limited private;

   -- Inserts Item into tree T.
   procedure Insert (T : in out Tree; Item : in Interval)
     with Global => null,
          Depends => (T => (T, Item));

   function Size (T : in Tree) return Natural
     with Global => null;

private
   pragma SPARK_Mode (Off);

   type Tree_Node;
   type Tree_Node_Access is access Tree_Node;
   type Tree_Node is
      record
         Data        : Interval;
         Maximum     : Float;
         Parent      : Tree_Node_Access := null;
         Left_Child  : Tree_Node_Access := null;
         Right_Child : Tree_Node_Access := null;
      end record;

   type Tree is new Ada.Finalization.Limited_Controlled with
      record
         Root  : Tree_Node_Access := null;
         Count : Natural := 0;
      end record;

   overriding procedure Finalize (T : in out Tree);

end Interval_Trees;
