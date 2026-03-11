with GPR2; use GPR2;
with GPR2.Project.Tree;

package Gnatprove_Build is

   --  This package contains types and subprograms related to the
   --  build process of Gnatprove.

   procedure Flow_Analysis_And_Proof
     (Tree : Project.Tree.Object; Status : out Integer);
   --  Call gnat2why on all relevant units in analysis mode, generating
   --  unit.spark file.

end Gnatprove_Build;
