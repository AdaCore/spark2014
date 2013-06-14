package body Alias is
   function Get_Content (R : My_Rec) return Element is
   begin
      return R.Content mod R.Modulus;
   end;

   function Add (R : My_Alias; X : Element) return Integer is
   begin
      return Get_Content (R) + X;
   end;
end Alias;
