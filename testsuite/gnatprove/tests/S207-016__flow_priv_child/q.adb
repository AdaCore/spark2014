with Q.Priv.Pub;
package body Q
  with Refined_State =>
  (State => Q.Priv.Pub.Pubs_State) is
   --  Refined_State should (indirectly) mention P.Priv.Pub.C
   procedure Dummy is null;
end;
