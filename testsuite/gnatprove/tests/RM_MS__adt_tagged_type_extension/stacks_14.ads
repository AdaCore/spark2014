package Stacks_14
  with SPARK_Mode
is
   type Stack is tagged private;

   function Is_Empty(S : Stack) return Boolean;
   function Is_Full(S : Stack) return Boolean;

   procedure Clear(S : out Stack)
     with Depends => (S    => null,
                      null => S);

   procedure Push(S : in out Stack; X : in Integer)
     with Depends => (S =>+ X);
   --  The =>+ symbolizes that any variable on the left side of =>+,
   --  depends on all variables that are on the right side of =>+
   --  plus itself. For example (X, Y) =>+ Z would mean that
   --  X depends on X, Z and Y depends on Y, Z.

   procedure Pop(S : in out Stack; X : out Integer)
     with Depends => ((S,X) => S);

private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1 .. Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack is tagged record
      Stack_Vector  : Vector;
      Stack_Pointer : Pointer_Range;
   end record;
end Stacks_14;
