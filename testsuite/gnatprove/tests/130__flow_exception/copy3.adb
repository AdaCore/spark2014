procedure Copy3 (A : Integer; Z : out Boolean)
  with Depends => (Z => A)
is
   procedure Try (X : Integer; By_Copy : out Boolean)
     with Import,
          Global => null,
          Always_Terminates => True,
          Exceptional_Cases => (Program_Error => X > 0);

begin
   --  If the following call executes normally, it makes Z dependent on A;
   --  if it raises an exception, then Z will remain uninitialized.
   Try (A, By_Copy => Z);
exception
   when Program_Error =>
      Z := not Z;  --  @INITIALIZED:CHECK
end;
