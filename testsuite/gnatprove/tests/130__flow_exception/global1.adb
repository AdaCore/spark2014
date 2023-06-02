procedure Global1 (A : Integer; Z : out Integer)
  with Depends => (Z => A)
is
   Proxy : Integer;
   --  A global object behaves as a by-reference parameter

   procedure Try (X : Integer)
     with Import,
          Global => (Output => Proxy),
          Always_Terminates => True,
          Exceptional_Cases => (Program_Error => X > 0);

begin
   --  Since Proxy is passed by reference, it must be written regardless of
   --  exception being raised.
   Try (A);
   Z := Proxy;
exception
   when Program_Error =>
      Z := Proxy;
end;
