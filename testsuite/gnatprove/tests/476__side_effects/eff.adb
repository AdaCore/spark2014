procedure Eff is

   type T is access Boolean;

   procedure Swap (X, Y : T)
      with Pre => True
   is
      Tmp : constant Boolean := X.all;
   begin
      X.all := Y.all;
      Y.all := X.all;
   end Swap;

   function Swap (X, Y : T) return Boolean
      with Side_Effects, Pre => True
   is
      Tmp : constant Boolean := X.all;
   begin
      X.all := Y.all;
      Y.all := X.all;
      return True;
   end Swap;

   A : T := new Boolean'(True);
   B : T := new Boolean'(False);
   C : Boolean;
begin
   Swap (A, B);
   C := Swap (A, B);
end;
