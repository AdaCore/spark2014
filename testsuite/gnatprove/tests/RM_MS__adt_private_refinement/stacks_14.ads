package Stacks_14
  with SPARK_Mode
is
   type Stack is private;

   function Is_Empty(S : Stack) return Boolean;
   function Is_Full(S : Stack) return Boolean;

   procedure Clear(S : in out Stack)
     with Post => Is_Empty(S);

   procedure Push(S : in out Stack; X : in Integer)
     with Pre  => not Is_Full(S),
          Post => not Is_Empty(S);

   procedure Pop(S : in out Stack; X : out Integer)
     with Pre  => not Is_Empty(S),
          Post => not Is_Full(S);

private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1 .. Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack is record
      Stack_Vector  : Vector;
      Stack_Pointer : Pointer_Range;
   end record;
end Stacks_14;
