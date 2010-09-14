package body ADT_Stack
is

   function Is_Empty(S : Stack) return Boolean
   is
   begin
      return S.Stack_Top = 0;
   end; -- the name of subprograms can be generated if missing

   function Is_Full(S : Stack) return Boolean
   is
   begin
      return S.Stack_Top = Stack_Size;
   end Is_Full;

   procedure Clear(S : out Stack)
   is
   begin
      S.Stack_Top :=0;
      S.Stack_Vector := (others => 0); -- The aggregat must be qualified
   end Clear;

   procedure Push(S : in out Stack; X : in Integer)
   is
   begin
      S.Stack_Top :=S.Stack_Top + 1;
      S.Stack_Vector(S.Stack_Top) := X;
   end Push;

   procedure Pop(S : in out Stack; X : out Integer)
   is
   begin
      X := S.Stack_Vector(S.Stack_Top);
      S.Stack_Top :=S.Stack_Top - 1;
   end Pop;

end ADT_Stack;

