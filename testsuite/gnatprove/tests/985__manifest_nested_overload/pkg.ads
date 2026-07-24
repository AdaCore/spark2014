package Pkg
  with SPARK_Mode
is
   Sink : Integer := 0;

   --  Two overloads of Set, told apart only by their profile. Each body nests
   --  a subprogram Helper with the *same* profile, so the dotted path
   --  "Pkg.Set.Helper" cannot say which overload's Helper it means: only the
   --  enclosing Set overload distinguishes them. A flat manifest entry is
   --  therefore ambiguous, while a manifest that nests the Helper rule inside
   --  the right Set rule resolves each Helper to its own overload.

   procedure Set (X : Integer)
   with Post => Sink >= 0;

   procedure Set (X : Boolean)
   with Post => Sink = (if X then 1 else 0);
end Pkg;
