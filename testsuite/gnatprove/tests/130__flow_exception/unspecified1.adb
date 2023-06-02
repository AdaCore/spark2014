procedure Unspecified1 (A : Integer; Z : out Integer)
  with Depends => (Z => A)
is
   type T is record
      C : Integer;
   end record;
   --  A type which is neither by-copy nor by-reference

   procedure Try (X : Integer; By_Unspecified : out T)
     with Import,
          Global => null,
          Always_Terminates => True,
          Exceptional_Cases => (Program_Error => X > 0);

   Proxy : T;

begin
   --  If the following call executes normally, it makes Z dependent on A;
   --  if it raises an exception, then the parameter will be uninitialized.
   Try (A, By_Unspecified => Proxy);
   Z := Proxy.C;
exception
   when Program_Error =>
      Z := Proxy.C; --  @INITIALIZED:CHECK
end;
