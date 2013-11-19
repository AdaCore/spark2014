package body Stacks_14
  with SPARK_Mode
is
   -- Expression function has default refined postcondition of
   -- Is_Empty'Result = (S.Stack_Pointer = 0)
   function Is_Empty(S : Stack) return Boolean is (S.Stack_Pointer = 0);

   -- Expression function has default refined postcondition of
   -- Is_Empty'Result = (S.Stack_Pointer = Stack_Size)
   function Is_Full(S : Stack) return Boolean is (S.Stack_Pointer = Stack_Size);

   procedure Clear(S : in out Stack) is
   begin
      S.Stack_Pointer := 0;
   end Clear;

   procedure Push(S : in out Stack; X : in Integer) is
   begin
      S.Stack_Pointer := S.Stack_Pointer + 1;
      S.Stack_Vector(S.Stack_Pointer) := X;
   end Push;

   procedure Pop(S : in out Stack; X : out Integer) is
   begin
      X := S.Stack_Vector(S.Stack_Pointer);
      S.Stack_Pointer := S.Stack_Pointer - 1;
   end Pop;
end Stacks_14;
