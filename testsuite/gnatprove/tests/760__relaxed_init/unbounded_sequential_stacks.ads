--  This package provides stack abstractions that have a capacity limited only
--  by available memory.  These stacks are not thread-safe.

generic
   type Element is private;
package Unbounded_Sequential_Stacks with SPARK_Mode is

   type Stack is tagged limited private;

   procedure Push (Onto : in out Stack; Item : in Element);

   procedure Pop (From : in out Stack; Item : out Element);

   procedure Pop (This : in out Stack);
   --  Removes from This stack the last element added

   Underflow : exception;

   function Depth (This : Stack) return Natural;

   function Empty (This : Stack) return Boolean;

   type Reference is access all Element;

   function Top (This : Stack) return Reference;
   --  Provides access to the top element in the stack (the last element pushed)
   --  without requiring that element to be first removed from the stack

private

   type Node;

   type List is access Node;

   type Node is
      record
         Value : aliased Element;
         Next  : List;
      end record;

   type Stack is tagged limited
      record
         Head  : List;
         Count : Natural := 0;
      end record;

end Unbounded_Sequential_Stacks;
