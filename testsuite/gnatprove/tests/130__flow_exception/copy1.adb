procedure Copy1 (A, B : Integer; Z : out Integer)
  with Depends => (Z => (A, B))
is
   procedure Try (X : Integer; By_Copy : out Integer)
     with Import,
          Global => null,
          Always_Terminates => True,
          Exceptional_Cases => (Program_Error => X > 0);

begin
   --  If the following call executes normally, it makes Z dependent on A;
   --  if it raises an exception, then hanlder will make Z dependent on B.
   Try (A, By_Copy => Z);
exception
   when Program_Error =>
      Z := B;
end;
