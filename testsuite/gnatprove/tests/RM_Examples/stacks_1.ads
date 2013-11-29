package Stacks_1
  with SPARK_Mode
is
   type Stack_Type is private;

   function Is_Empty (S : Stack_Type) return Boolean;
   --  Default postcondition is True.

   function Is_Full (S : Stack_Type) return Boolean;
   --  Default postcondition is True.

   procedure Push (S : in out Stack_Type; I : in Integer)
     with Pre  => not Is_Full (S),
          Post => not Is_Empty (S);

   procedure Pop (S : in out Stack_Type)
     with Post => not Is_Full (S);

   function Top (S : Stack_Type) return Integer
     with Pre => not Is_Empty (S);
private
   --  Full type declaration of private type.
   Stack_Size : constant := 100;

   type Pointer_Type is range 0 .. Stack_Size;
   subtype Stack_Index is Pointer_Type range 1 .. Pointer_Type'Last;
   type Stack_Array is array (Stack_Index) of Integer;

   --  All stack objects have default initialization.
   type Stack_Type is record
      Pointer : Pointer_Type := 0;
      Vector  : Stack_Array := (others => 0);
   end record;
end Stacks_1;
