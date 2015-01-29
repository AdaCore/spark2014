procedure Useless_Annot is
   X : Integer := 0;
   pragma Annotate (Gnatprove, Intentional, "does not trigger", "");
   --  this pragma should trigger a warning because it does not correspond to
   --  a check

   function Posit (X : Integer) return Integer
      with Pre  => X < Integer'Last,
           Post => Posit'Result > X;

   function Posit (X : Integer) return Integer is
   begin
      return X + 1;
   end Posit;

   Z : Natural := Posit (1);
   pragma Annotate (Gnatprove, Intentional, "range check", "");
   --  this pragma should not trigger a warning because it corresponds to a
   --  check
begin
   null;
end Useless_Annot;
