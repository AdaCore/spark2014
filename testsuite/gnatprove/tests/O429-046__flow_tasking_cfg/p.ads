package P is
   protected PO1 is
      function Get_Content return Integer;

      procedure Set_Content (X : Integer);

      procedure Swap_Content;  --  Illegal in SPARK
   private
      Content : Integer := 0;
   end PO1;
end P;
