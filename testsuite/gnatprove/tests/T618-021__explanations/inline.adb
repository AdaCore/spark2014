procedure Inline with SPARK_Mode is

   --  Two mutually recursive subprograms that get inlined-for-proof.
   --
   --  (The silly "if True then ..." is prevents frontend from detecting
   --  infinite recursion.)
   --
   --  Due to inlining A is reprorted as recursive and thus nonterminating,
   --  while B is reported as terminating, because there the annotation on A
   --  is trusted.

   procedure A with Annotate => (GNATprove, Terminating);

   procedure B with Annotate => (GNATprove, Terminating) is
   begin
      if True then A; end if;
   end B;

   procedure A is
   begin
      if True then B; end if;
   end;
begin
   null;
end;
