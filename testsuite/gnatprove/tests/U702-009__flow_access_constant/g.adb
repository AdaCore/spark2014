procedure G is
   type T is access Boolean;
   generic
      X : T;
   package Gen with Initializes => (Y => X) is
      Y : T := X;
   end;

   package Inst is new Gen (null);
begin
   null;
end;
