package body P is
   procedure A (Cond : Boolean) is
   begin
      X := 0;
      if Cond then A (not Cond); end if;
      Y := X;
   end;

   procedure B (A : in out Natural; Cond : Boolean) is
   begin
      X := 0;
      if Cond then B (A, not Cond); end if;
   end B;

   function C (A : Natural; Cond : Boolean) return Natural is
   begin
      X := 0;
      return C (A, not Cond);
   end C;
end;
