with Types; use Types;

function Blob (Val : Integer) return Boolean
is
   X : Ptr := new Integer'(Val);
   Z : Ptr := X;
begin
   if Z.all > 10 then
      return Res : Boolean do
        X := Z;
        Res := True;
      end return;
   end if;

   Z.all := Z.all * 2;

   X := Z;

   return True;
end Blob;
