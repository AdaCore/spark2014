package P is
   type T (D : Integer) is record
      C : Integer;
   end record;
   --  A non-null record type with a discriminant (unconstrained)

   subtype T1 is T (D => 1);
   --  Same type but with a fixed discriminant (constrained)

   procedure Proc  (X : out T);
   procedure Proc1 (X : out T1);
   --  Procedures that write objects of both types
end;
