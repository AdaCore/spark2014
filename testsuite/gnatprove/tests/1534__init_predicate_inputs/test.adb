procedure Test (Minimum : Integer) with SPARK_Mode is
   type Item is record
      Value : Integer;
   end record
   with Dynamic_Predicate => Item.Value >= Minimum;

   procedure Initialize_Item (X : out Item; Value : Integer)
   with
     Relaxed_Initialization => X,
     Pre => Value >= Minimum,
     Post => X'Initialized -- @POSTCONDITION:PASS
   is
   begin
      X := (Value => Value);
   end Initialize_Item;

   type Node;
   type Node_Access is access Node;
   type Node is record
      Value : Integer;
      Next : Node_Access;
   end record
   with Dynamic_Predicate => Node.Value >= Minimum;

   procedure Initialize_Node (X : out Node; Value : Integer)
   with
     Relaxed_Initialization => X,
     Pre => Value >= Minimum,
     Post => X'Initialized -- @POSTCONDITION:PASS
   is
   begin
      X := (Value => Value, Next => null);
   end Initialize_Node;
begin
   null;
end Test;
