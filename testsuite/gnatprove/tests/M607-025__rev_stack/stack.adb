package body Stack is
   pragma SPARK_Mode (On);

   package body Model is
      function To (S : Stack) return M is (M(S.Content (1 .. S.Top)));
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

   function Empty_Stack return Stack
   is
      E : Stack;
   begin
      E.Top := 0;
      E.Content := Intarray'(R2 => 0);
      return E;
   end Empty_Stack;

end Stack;
