
-- Package Inst, instantiating G with Pred
with G;
with Pred;
pragma Elaborate_All (G);
package Inst is
  package MI is new G (Pred.A_Subtype);
end;
