with Other;
pragma Elaborate_All (Other);

package Const
  with Initializes => (B => (Other.V, Other.C))
is
   B : constant Integer := Other.Gimme_V_Plus_C;

end Const;
