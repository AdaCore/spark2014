package P is

   task type TT (X : Integer);

   subtype TT1 is TT (1);
   TO1 : TT (1);

   Foo : constant Boolean := TO1 in TT1;

end;
