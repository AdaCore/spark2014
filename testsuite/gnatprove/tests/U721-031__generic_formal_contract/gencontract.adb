pragma Ada_2022;

procedure Gencontract is

   generic
     with function Id (X : Integer) return Integer
       with Post => Id'Result /= X;
   procedure Wrapper (Y : Integer);

   procedure Wrapper (Y : Integer) is
   begin
      pragma Assert (Id (Y) = Y);
   end Wrapper;

   function Ident (X : Integer) return Integer
     with Post => Ident'Result = X
   is
   begin
      return X;
   end Ident;

   procedure Local is new Wrapper (Ident);

begin
   Local (42);
end Gencontract;
