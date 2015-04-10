package Stacks_14
  with SPARK_Mode
is
   type Stack is private;

   function Is_Empty(S : Stack) return Boolean;
   function Is_Full(S : Stack) return Boolean;

   procedure Clear(S : out Stack);
   procedure Push(S : in out Stack; X : in Integer);
   procedure Pop(S : in out Stack; X : out Integer);

private
   Stack_Size : constant := 100;
   type Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range is Pointer_Range range 1 .. Stack_Size;
   type Vector is array(Index_Range) of Integer;

   type Stack is record
      Stack_Vector : Vector;
      Stack_Pointer : Pointer_Range;
   end record;
end Stacks_14;
