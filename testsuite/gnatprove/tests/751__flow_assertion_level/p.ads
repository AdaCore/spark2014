package P is
   procedure Set_Item  (X : Boolean);
   procedure Set_Item1 (X : Boolean);
   procedure Set_Item2 (X : Boolean);

   function Get_Item  return Boolean with Ghost;
   function Get_Item1 return Boolean with Ghost;
   function Get_Item2 return Boolean with Ghost;

   procedure Flip;
end;
