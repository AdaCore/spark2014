with P.PC1.Q;
with P.PC2.Q;
package body P with Refined_State => (State => (P.PC1.Q.X, P.PC2.Q.Y)) is
   procedure Dummy is null;
end;
