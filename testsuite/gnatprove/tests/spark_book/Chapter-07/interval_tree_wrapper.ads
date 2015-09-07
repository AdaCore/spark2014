with Interval_Tree;
package Interval_Tree_Wrapper
   with
      SPARK_Mode     => On,
      Abstract_State => Underlying_Tree,
      Initializes    => Underlying_Tree
is

   type Interval is new Interval_Tree.Interval;

   type Status_Type is (Success, Insufficient_Space, Logical_Error);

   -- Inserts Item into the tree.
   procedure Insert (Item   : in  Interval;
                     Status : out Status_Type)
     with
       Global  => (In_Out => Underlying_Tree),
       Depends => (Underlying_Tree => (Underlying_Tree, Item),
                   Status => Underlying_Tree),
       Post    => (Size'Old = (if Status = Success then Size - 1 else Size));

   function Size return Natural
     with
       Global => (Input => Underlying_Tree);

   -- Destroys the tree. After this call the tree can be reused.
   procedure Destroy
     with
       Global => (In_Out => Underlying_Tree),
       Post   => Size = 0;

end Interval_Tree_Wrapper;
