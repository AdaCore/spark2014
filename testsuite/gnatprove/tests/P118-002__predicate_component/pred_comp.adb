procedure Pred_Comp is

   type CT is null record with Predicate => False;

   type R is record
      C : CT;
   end record;

   RO : R;

   procedure Inner (X : CT);

   -----------
   -- Inner --
   -----------

   procedure Inner (X : CT) is
   begin
      null;
   end;

begin
   Inner (RO.C);
end;
