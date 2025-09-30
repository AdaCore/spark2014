pragma Assertion_Level (L1);
pragma Assertion_Level (L2);

package body P is
   --  Create objects with declared ghost assertion levels

   Item  : Boolean := True with Ghost;
   Item1 : Boolean := True with Ghost => L1;
   Item2 : Boolean := True with Ghost => L2;

   procedure Set_Item  (X : Boolean) is
   begin
      Item  := X;
   end;

   procedure Set_Item1 (X : Boolean) is
   begin
      Item1 := X;
   end;

   procedure Set_Item2 (X : Boolean) is
   begin
      Item2 := X;
   end;

   function Get_Item  return Boolean is (Item);
   function Get_Item1 return Boolean is (Item1);
   function Get_Item2 return Boolean is (Item2);

   procedure Flip is
   begin
      Item  := not Item;
      Item1 := not Item1;
      Item2 := not Item2;
   end;

end P;
