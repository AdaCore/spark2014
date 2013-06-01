package body Length is

   function F return Boolean is
      X : Constr_Ar;
      Res : Boolean;
   begin
      if X'Length = 20 then
         Res := True;
      else
         Res := False;
      end if;
      return Res;
   end F;

   function G return Integer is
      X : Constr_Ar;
   begin
      return X'Length;
   end G;

   procedure UF (X : Unconstr_Ar)
   is
   begin
      B := (X'Length = 20);
   end UF;
end Length;
