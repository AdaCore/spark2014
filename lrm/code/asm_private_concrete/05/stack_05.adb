package body Stack_05
is
   procedure Push(X : in Integer)
   is
   begin
      Pointer := Pointer + 1;
      S(Pointer) := X;
   end Push;

   procedure Pop(X : out Integer)
   is
   begin
      X := S(Pointer);
      Pointer := Pointer - 1;
   end Pop;
end Stack_05;
