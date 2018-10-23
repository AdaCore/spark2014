private generic
package Gen.PC is
   X : Gen.T; pragma Assert (X.C = 0);
   --  Private child can see the private part of its parent,
   --  i.e. the component in the full type declaration of T.
   --
   --  However, this package is analysed with FA.B_Scope set to either the
   --  private part or the body part, which get visibility of the parent's
   --  private declaration via dedicated visibility rules. This declaration
   --  alone is thus not enough to test the visibility from the public part.

   package Inner with Initializes => Y is
      Y : Gen.T := X'Update (C => 0); pragma Assert (Y.C = 0);
      --  Here the situation is similar, i.e. the full type declaration of T
      --  can be seen, but the visibility must come from the enclosing scope,
      --  i.e. the public part of Gen.PC.
   end;
end;
