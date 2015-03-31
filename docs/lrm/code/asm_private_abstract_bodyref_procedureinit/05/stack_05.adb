package body Stack_05
--# own State is S, Pointer;
is
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   Pointer : Pointer_Range;
   S       : Vector;

   procedure Push(X : in Integer)
   --# global in out Pointer, S;
   is
   begin
      Pointer := Pointer + 1;
      S(Pointer) := X;
   end Push;

   procedure Pop(X : out Integer)
   --# global in     S;
   --#        in out Pointer;
   is
   begin
      X := S(Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Init
   --# global    out Pointer, S;
   is
   begin
      Pointer := 0;
      S := Vector'(Index_Range => 0);
   end Init;
end Stack_05;
