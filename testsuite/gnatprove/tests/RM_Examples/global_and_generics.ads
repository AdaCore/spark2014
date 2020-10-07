package Global_And_Generics is

   generic
      X : Integer;
   package G is
      procedure P (Y : in out Integer) with
        Global  => X,
        Depends => (Y =>+ X);
   end G;

   procedure Q (Z : in out Integer) with
     Global  => null,
     Depends => (Z =>+ null);

end Global_And_Generics;
