package body Misplaced is

   pragma Annotate (gnatprove, Force);

   procedure P is

      --  Various incorrect annotations
      pragma Annotate (gnatprove);
      pragma Annotate (gnatprove, Bad);
      pragma Annotate (gnatprove, Force, 2);
      pragma Annotate (gnatprove, Bad, "something");

      --  Redundant annotation
      pragma Annotate (gnatprove, Force);

      type T is access Integer;
      X : T := new Integer;

      --  Contradictory annotation
      pragma Annotate (gnatprove, Ignore);
   begin
      X.all := 0;
   end P;
end Misplaced;
