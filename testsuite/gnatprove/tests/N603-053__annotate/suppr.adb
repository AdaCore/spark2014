package body Syntax is

   procedure P (C : Boolean) is
      X : Integer;
      Z : Integer;
   begin
      if C then
         X := 1;
      end if;
      if X < 0 then
         X := Z;
      end if;
      pragma Annotate (Gnatprove, Intentional,"""X"" might not be initialized","");
      pragma Annotate (Gnatprove, Intentional,"""Z"" is not initialized","");
   end P;

   procedure Q (C : Boolean) is
      X : Integer;
      Z : Integer;
   begin
      if C then
         X := 1;
      end if;
      if X < 0 then
         pragma Annotate (Gnatprove, Intentional,"""X"" might not be initialized","");
         X := Z;
         pragma Annotate (Gnatprove, Intentional,"""Z"" is not initialized","");
      end if;
   end Q;
end Syntax;
