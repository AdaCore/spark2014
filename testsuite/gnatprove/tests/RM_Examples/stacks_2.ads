package Stacks_2
  with SPARK_Mode,
       Abstract_State => The_Stack,
       Initializes    => The_Stack
is
   function Is_Empty return Boolean
     with Global => The_Stack;
   --  Default postcondition is True.

   function Is_Full return Boolean
     with Global => The_Stack;
   --  Default postcondition is True.

   procedure Push (I : Integer)
     with Global => (In_Out => The_Stack),
          Pre    => not Is_Full,
          Post   => not Is_Empty;

   procedure Pop
     with Global => (In_Out => The_Stack),
     Post   => not Is_Full;

   function Top return Integer
     with Global => The_Stack,
          Pre    => not Is_Empty;
   --  Default postcondition is True.
private
   --  Full type declaration of private type for usage (1).
   Stack_Size : constant := 100;

   type Pointer_Type is range 0 .. Stack_Size;
   subtype Stack_Index is Pointer_Type range 1 .. Pointer_Type'Last;
   type Stack_Array is array (Stack_Index) of Integer;

   --  All stack objects have default initialization.
   type Stack_Type is record
      Pointer : Pointer_Type := 0;
      Vector  : Stack_Array := (others => 0);
   end record;
end Stacks_2;
