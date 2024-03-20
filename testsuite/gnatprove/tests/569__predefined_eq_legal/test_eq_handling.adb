procedure Test_Eq_Handling with SPARK_Mode is

   --  The annotation on T is incorrect. The predefined equality of T with
   --  C should not be handled as the logical equality.

   package Bad_Annot is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
      function Sign (X : T) return Boolean;
      D : constant T;
   private
      pragma SPARK_Mode (Off);
      type T is new Float;
      C : constant T := 0.0;
      function Sign (X : T) return Boolean is
         (T'Copy_Sign (1.0, X) >= 0.0);
      D : constant T := -0.0;
   end Bad_Annot;
   use Bad_Annot;

   procedure Test (X : T) with
     Global => null,
     Post => (if X = C then Sign (X) = Sign (C)); --@POSTCONDITION:PASS
   --  The postcondition of Test is proved, but fails at runtime

   procedure Test (X : T) is null;
begin
   Test (D);
end Test_Eq_Handling;
