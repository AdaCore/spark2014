package P is
   type R1 is record
      C1 : Boolean;
   end record;

   type R2 is record
      C2 : R1;
   end record;

   --  The idea is to have nested records (that's why a type R2)
   --  and use them in both protected and non-protected subprograms.

   --  The explicit Global => null is to keep global generation away;
   --  the explicit Depends is intentionally wrong to emit IDE traces
   --  with explanations.

   protected type PT is
      procedure Flip with Global => null, Depends => (PT => null, null => PT);
   private
      C3 : R2 := (C2 => (C1 => True));
   end PT;

   procedure Flip (C3 : in out R2) with Global => null, Depends => (C3 => null, null => C3);
end P;
