package body The_Stack_With_More_Conditions
--# own State is S, Pointer;          -- State refinement
is
   Max_Stack_Size: constant := 1024;
   type    Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range   is Pointer_Range
   range 1 .. Max_Stack_Size;
   type	   Vector        is array (Index_Range) of Integer;

   S : Vector;                        -- Declaration of constituents
   Pointer: Pointer_Range;

   -- The subprogram contracts are refined in terms of the constituents.
   -- Expression functions could be used where applicable

   function Is_Empty return Boolean
   --# global Pointer;
   --# return Pointer =  0;
   is
   begin
      return Pointer = 0;
   end Is_Empty;

   function Is_Full return Boolean
   --# global Pointer;
   --# return Pointer =  Max_Stack_Size;
   is
   begin
      return Pointer = Max_Stack_Size;
   end Is_Full;

   function Top return Integer
   --# global Pointer, S;
   --# pre not Is_Empty (Pointer);
   --# return S (Pointer);
   is
   begin
      return S (Pointer);
   end Top;

   procedure Push(X: in Integer)
   --# global in out Pointer, S;
   --# pre not Is_Full (Pointer);
   --# post Top (Pointer,S) = X;
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
   --# global in     S;
   --#	      in out Pointer;
   --# pre not Is_Empty(Pointer);
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Swap (X: in Integer)
   --# global in     Pointer;
   --#        in out S;       -- We cannot have conditional global contracts in SPARK 2005.
   --# pre not Is_Empty(Pointer);
   --# post Top(Pointer,S) = X;
   is
   begin
      S (Pointer) := X;
   end Swap;


begin -- Initialization - we promised to initialize the state
   Pointer := 0;
   S := Vector'(Index_Range => 0);
end The_Stack_With_More_Conditions;
