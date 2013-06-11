package body Stack is

   ----------
   -- Push --
   ----------

   function Push
     (S : Stack;
      X : in Integer)
      return Stack
   is

   begin
--      return Res : Stack := Stack'(S.Top + 1, S.Content) do
--         Res.Content (Res.Top) := X;
--      end return;
      declare
         Res : Stack := Stack'(S.Top + 1, S.Content);
      begin
         Res.Content (Res.Top) := X;
         return Res;
      end;
   end Push;

   ----------
   -- Push --
   ----------

   procedure Push
     (S : in out Stack;
      X : in Integer)
   is
   begin
      S.Top := S.Top + 1;
      S.Content (S.Top) := X;
   end Push;

   ---------
   -- Pop --
   ---------

   procedure Pop
     (S : in out Stack)
   is
   begin
      S.Top := S.Top - 1;
   end Pop;

end Stack;
