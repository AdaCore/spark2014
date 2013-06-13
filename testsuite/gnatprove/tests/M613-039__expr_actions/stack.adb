package body Stack is

   package body Model is
      function To (S : Stack) return M is (M(S.Content (1 .. S.Top)));
      function To_But_Top (S : Stack) return M is (M(S.Content (1 .. S.Top - 1)));

      function Is_Full  (S : Stack) return Boolean is (S.Top >= S.Content'Last);
      function Is_Empty (S : Stack) return Boolean is (S.Top < S.Content'First);
   end Model;

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
