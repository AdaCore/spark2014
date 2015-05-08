with Other;
pragma Elaborate_All (Other);

package Const
  with Initializes => (A => (Other.V),
                       B => (Other.V, Other.C),
                       C => (Other.V, Other.C))
is
   A : constant Integer := Other.V;
   B : constant Integer := Other.Gimme_V_Plus_C;
   C : constant Integer := B;
   D : constant Integer := Other.Gimme_C;
   E : constant Integer := Other.Identity (Other.Identity (Other.C));
   F : constant Integer := 0;
   G : constant Integer := Other.Gimme_Zero;
   H : constant Integer := F;
   I : constant Integer := Other.Identity (Other.S);

   function Add_Everything return Integer
     with Global => (A, B, C, D, E);
end Const;
