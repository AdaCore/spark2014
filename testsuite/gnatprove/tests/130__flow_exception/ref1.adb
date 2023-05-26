procedure Ref1 (A : Integer; Z : out Integer)
  with Depends => (Z => A)
is
   type T is limited record
      C : Integer;
   end record;
   --  An explicitly limited record is a by-reference type; RM 6.2(7/3).

   procedure Try (X : Integer; By_Ref : out T)
     with Import,
          Global => null,
          Always_Terminates => True,
          Exceptional_Cases => (Program_Error => X > 0);

   Proxy : T;

begin
   --  Since Proxy is passed by reference, it must be written regardless of
   --  exception being raised.
   Try (A, By_Ref => Proxy);
   Z := Proxy.C;
exception
   when Program_Error =>
      Z := Proxy.C;
end;
