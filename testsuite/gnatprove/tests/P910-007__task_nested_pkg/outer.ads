package Outer is

   X : Boolean := False;

   task type TT;

   package Inner is
      T : TT;
   end;
end;
