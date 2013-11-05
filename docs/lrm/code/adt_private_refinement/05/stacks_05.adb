package body Stacks_05 is

   function Is_Empty (S : Stack) return Boolean
   --# return S.Stack_Pointer = 0;
   is
   begin
      return S.Stack_Pointer = 0;
   end Is_Empty;

   function Is_Full (S : Stack) return Boolean
   --# return S.Stack_Pointer = Stack_Size;
   is
   begin
      return S.Stack_Pointer = Stack_Size;
   end Is_Full;

   procedure Clear (S : in out Stack)
   --# post Is_Empty(S);
   is
   begin
      S.Stack_Pointer := 0;
   end Clear;

   procedure Push (S : in out Stack; X : in Integer)
   is
   begin
      S.Stack_Pointer := S.Stack_Pointer + 1;
      S.Stack_Vector (S.Stack_Pointer) := X;
   end Push;

   procedure Pop (S : in out Stack; X : out Integer)
   is
   begin
      X := S.Stack_Vector (S.Stack_Pointer);
      S.Stack_Pointer := S.Stack_Pointer - 1;
   end Pop;
end Stacks_05;
