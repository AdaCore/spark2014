package body Pedantic
is

   function Alignment_Of_R return Natural
   is
   begin
      return R'Alignment;
   end Alignment_Of_R;

   function Order_Of_R return System.Bit_Order
   is
   begin
      return R'Bit_Order;
   end Order_Of_R;

   function CS_Of_A return Natural
   is
   begin
      return A'Component_Size;
   end CS_Of_A;

   function First_Bit_Of_F1 return Natural
   is
   begin
      return V.F1'First_Bit;
   end First_Bit_Of_F1;

   function Last_Bit_Of_F1 return Natural
   is
   begin
      return V.F1'Last_Bit;
   end Last_Bit_Of_F1;

   function Position_Of_F1 return Natural
   is
   begin
      return V.F1'Position;
   end Position_Of_F1;

   function Size_Of_A return Natural
   is
   begin
      return A'Size;
   end Size_Of_A;

   function Size_Of_V return Natural
   is
   begin
      return V'Size;
   end Size_Of_V;


end Pedantic;
