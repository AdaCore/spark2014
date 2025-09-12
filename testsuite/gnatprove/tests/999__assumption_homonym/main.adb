procedure Main is
   function F return Boolean with Pre => True is
   begin
      return True;
   end;

   procedure P (X : Integer) with Pre => F; procedure P (X : Float) with Pre => F;

   procedure P (X : Integer) is null;
   procedure P (X : Float) is null;

begin
   P (0);
   P (0.0);
end;
