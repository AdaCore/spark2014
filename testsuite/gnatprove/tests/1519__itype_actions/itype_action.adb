procedure Itype_Action (N : Positive) with SPARK_Mode is
   type String_Access is access String;
   type Rec is record
      P : String_Access (1 .. N);
   end record;

   --  Freeze Rec in the declare expression so its constrained component type
   --  produces an itype reference in the expression actions.

   B : constant Boolean :=
     (declare
        X : constant Rec := (P => null);
      begin
        X.P = null);
begin
   pragma Assert (B);
end Itype_Action;
