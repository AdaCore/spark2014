package body P is
   function F (X, Y : T; Z : Boolean := Default) return T is
      T : Boolean := Z;
   begin
      return F(X, T);
   end F;
   procedure Proc (X : in out T) is
   begin
      X := F(X);
   end Proc;
   function F (X : T; Y : Boolean := Default) return T is
      T : Boolean := Y;
   begin
      return X;
   end F;
end P;
