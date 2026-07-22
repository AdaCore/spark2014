package Pkg
  with SPARK_Mode
is
   type T is new Integer;

   --  A user-defined operator that is not overloaded. A proof-manifest entry
   --  can target it by its quoted path alone (Pkg."&"), with no profile.

   function "&" (X, Y : T) return T
   with Post => "&"'Result = T'Max (X, Y);

   --  Two overloads of "-", one binary and one unary. They share the dotted
   --  path Pkg."-" and are told apart only by their profile, exactly like the
   --  overloaded identifier subprograms. Each per-overload entry must apply to
   --  its own overload only.

   function "-" (X, Y : T) return T
   with Post => "-"'Result = T'Max (X, Y);

   function "-" (X : T) return T
   with Post => "-"'Result = X;
end Pkg;
