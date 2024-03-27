package body Stacks
  with SPARK_Mode
is
   procedure Push (S : in out Stack; E : Element) is
   begin
      S.Content (S.Top + 1) := E;
      S.Top := S.Top + 1;
   end Push;

   function Pop (S : in out Stack) return Element is
      E : Element := S.Content (S.Top);
   begin
      S.Top := S.Top - 1;
      return E;
   end Pop;

end Stacks;
