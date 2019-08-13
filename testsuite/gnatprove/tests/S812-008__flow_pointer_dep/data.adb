package body Data is
   procedure Copy_Pointer (A : in AAI; B : out AI) is --move (A) (B)
   begin
      B     := A.all; --move of (A.all.all) occurs here
      A.all := null;
   end Copy_Pointer;
end Data;
