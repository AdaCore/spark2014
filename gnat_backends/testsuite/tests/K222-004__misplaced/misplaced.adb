package body Misplaced is

   pragma Annotate (Formal_Proof, On);

   procedure P is

      --  Various incorrect annotations
      pragma Annotate (Formal_Proof);
      pragma Annotate (Formal_Proof, Bad);
      pragma Annotate (Formal_Proof, On, 2);
      pragma Annotate (Formal_Proof, Bad, "something");

      --  Redundant annotation
      pragma Annotate (Formal_Proof, On);

      type T is access Integer;
      X : T := new Integer;

      --  Contradictory annotation
      pragma Annotate (Formal_Proof, Off);
   begin
      X.all := 0;
   end P;
end Misplaced;
