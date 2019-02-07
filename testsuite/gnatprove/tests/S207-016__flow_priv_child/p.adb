package body P with Refined_State => (State => null) is
   --  Refined_State should (indirectly) mention P.Priv.Pub.C
   procedure Dummy is null;
end;
