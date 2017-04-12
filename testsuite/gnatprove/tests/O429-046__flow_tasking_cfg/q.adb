with P; use P;

package body Q is
   protected body PO2 is
      function Get_Content return Integer is (Content);

      procedure Set_Content (X : Integer) is
      begin
         Content := X;
      end Set_Content;

      procedure Swap_Content is
         Tmp : Integer := Content;
         Cont : Integer := PO1.Get_Content;
      begin
         Set_Content (Cont);
         PO1.Set_Content (Tmp);
      end Swap_Content;
   end PO2;
end Q;
