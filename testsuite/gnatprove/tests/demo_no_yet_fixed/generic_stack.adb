package body Generic_Stack
is
   --# hide  Generic_Stack
   -- Examiner does not analyse the body because a generic packages,
   -- are not supported by SPARK.

   type Vector is array (Positive range <>) of Item;
   Stack_Vector : Vector(1 .. Stack_Size);
   Index : Natural := 0;

   procedure Push(E : in Item) is
   begin
      if Index >= Stack_Size then
         raise Overflow;
      end if;
      Index := Index + 1;
      Stack_Vector(Index) := E;
   end Push;

   procedure Pop(E : out Item) is
   begin
      if Index = 0 then
         raise Underflow;
      end if;
      E := Stack_Vector(Index);
      Index := Index - 1;
   end Pop;

end Generic_Stack;
