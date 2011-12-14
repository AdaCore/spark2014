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
      if Is_Full (S) then
         raise Overflow;  -- raise exception
      end if;
      S.Stack_Top :=S.Stack_Top + 1;
      S.Stack_Vector(S.Stack_Top) := X;
   end Push;

   procedure Pop(S : in out Stack; X : out Integer)
   is
   begin
      if Is_Empty (S) then
         raise Underflow;
      end if;
      X := S.Stack_Vector(S.Stack_Top);
      S.Stack_Top :=S.Stack_Top - 1;
   end Pop;

   function "=" (S,T : Stack) return Boolean
   is
   begin
      return    -- using Slicing; not yet translated
        S.Stack_Vector(1 .. S.Stack_Top) = T.Stack_Vector (1 .. T.Stack_Top);

   end "=";

   -- the followig should be a possible translation

   --     function "=" (S,T : Stack) return Boolean
   --     is
   --     begin
   --        if S.Stack_Top /= T.Stack_Top then
   --           return False;
   --        end if;
   --        for I in 1 .. S.Stack_Top Loop -- insert type in loop
   --           if S.Stack_Vector (I) /= T.Stack_Vector (I) then
   --              return False;
   --           end if;
   --        end loop;
   --        return True;
   --     end "=";

end ADT_Stack;

