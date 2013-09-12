--  Generic package

generic
   Stack_Size : Positive;
   type Item is private;
package Generic_Stack is pragma SPARK_Mode (On);  
   procedure Push(E : in  Item);
   procedure Pop (E : out Item);
   Overflow, Underflow : exception;
end Generic_Stack;
