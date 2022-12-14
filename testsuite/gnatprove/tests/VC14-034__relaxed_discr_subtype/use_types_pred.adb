with Types; use Types;

procedure Use_Types_Pred with SPARK_Mode is

   subtype PP is T with Predicate => (if PP.B then PP.X'Initialized);

   subtype PP_True is PP (True);

   procedure Check_Pred (X : PP_True) with
     Global => null
   is
   begin
      pragma Assert (X.X'Initialized);
   end Check_Pred;

   C : PP_True;

begin
   Check_Pred (C);  --  There should be an initialization or a predicate check
                    --  here.
end Use_Types_Pred;
