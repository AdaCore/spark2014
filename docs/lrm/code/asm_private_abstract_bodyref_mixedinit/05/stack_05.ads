package Stack_05
--# own Stack;
--# initializes Stack;
is
   procedure Push(X : in Integer);
   --# global in out Stack;

   procedure Pop(X : out Integer);
   --# global in out Stack;
private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;
end Stack_05;
