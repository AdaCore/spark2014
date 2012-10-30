package Stack_05
--# own State;
is
   procedure Push(X : in Integer);
   --# global in out State;

   procedure Pop(X : out Integer);
   --# global in out State;

   procedure Init;
   --# global    out State;
private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is
      record
         S : Vector;
         Pointer : Pointer_Range;
      end record;
end Stack_05;
