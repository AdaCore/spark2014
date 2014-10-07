package body Syntax is

   procedure P (C : Boolean) is
      X : Integer;
   begin
      if C then
         X := 1;
      end if;
      if X < 0 then
         null;
      end if;
      pragma Annotate (Gnatprove, Intentional);
      pragma Annotate (Gnatprove, Bla, "", "");
      pragma Annotate (Gnatprove, Intentional, X + 1, "");
      pragma Annotate (Gnatprove, Intentional, "", X + 1);
   end P;
end Syntax;
