-- This package implement an extension of the type adt_stack
-- with ADT_Stack; use ADT_Stack; -- inherite clause ?
package ADT_Stack.Child
is
   type Child_Stack is new ADT_Stack.Stack with private;

   procedure Clear(S : out Child_Stack);
   procedure Push(S : in out Child_Stack; X : in Integer);

   function Top_Identity(S : Child_Stack) return Integer;

private
   type Child_Stack is new ADT_Stack.Stack with
      record
         Child_Stack_Vector  : ADT_Stack.Vector;
         Next_Value     : Integer;
      end record;

end ADT_Stack.Child;
