procedure Copy2 (A, B : Integer; Z : out Integer)
  with Depends => (Z => (A, B))
is
   procedure Try (X : Integer; By_Copy : out Integer)
     with Import,
          Global => null,
          Always_Terminates => True,
          Exceptional_Cases => (Program_Error => X > 0);

begin
   --  The assignment makes Z dependent on A. If the subsequent call raises an
   --  exception, then Z will remain dependent on A; if it terminates normally,
   --  Z will become dependent on B.
   Z := A;
   Try (B, By_Copy => Z);
exception
   when Program_Error =>
      null;
end;
