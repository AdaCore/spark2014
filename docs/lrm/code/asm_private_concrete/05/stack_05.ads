package Stack_05
--# own S, Pointer;
is
   procedure Push(X : in Integer);
   --# global in out S, Pointer;

   procedure Pop(X : out Integer);
   --# global in     S;
   --#        in out Pointer;
private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   S : Vector;
   Pointer : Pointer_Range;
end Stack_05;
