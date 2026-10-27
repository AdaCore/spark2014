procedure Predicate_Inline with SPARK_Mode is
   type T is new Integer;

   function F (X : T) return Boolean with
     Post => F'Result = False, -- @POSTCONDITION:FAIL
     Annotate => (GNATprove, Inline_For_Proof);

   subtype S is T with Predicate => F (S);

   function F (X : T) return Boolean is
      --  The predicate on this uninitialized object is assumed at declaration.
      --  Inlining F as False would make that assumption inconsistent.
      V : S;
   begin
      return True;
   end F;
begin
   null;
end Predicate_Inline;
