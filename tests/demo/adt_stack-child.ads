-- This package implement an extension of the type adt_stack
-- with ADT_Stack; use ADT_Stack; -- inherite clause ?
package ADT_Stack.Child
is
   type Child_Stack is new ADT_Stack.Stack with
      record
         Next_Value     : Integer;
      end record;

   procedure Clear(S : out Child_Stack);
   procedure Push(S : in out Child_Stack; X : in Integer);

   function Top_Identity(S : Child_Stack) return Integer;

end ADT_Stack.Child;
