package Pkg
  with SPARK_Mode
is
   Sink : Integer := 0;

   --  Two overloads of Set, distinguished only by their profile. A proof
   --  manifest that targets them individually must carry a profile on each
   --  entry, and each entry must apply to its own overload only. Their bodies
   --  nest further subprograms -- including a nested pair of overloads -- so
   --  that a manifest can also target a subprogram nested in an overload, and
   --  overloads nested in an overload, each by its own profile.

   procedure Set (X : Integer)
   with Post => Sink >= 0;

   procedure Set (X : Boolean)
   with Post => Sink = (if X then 1 else 0);
end Pkg;
