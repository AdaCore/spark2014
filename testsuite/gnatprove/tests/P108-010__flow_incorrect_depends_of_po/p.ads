package P is
   protected type PO_Type is
      procedure Set (X : Integer)
        with Depends => (PO_Type =>+ X);

      function Get return Integer;
   private
      Content : Integer := 0;
   end PO_Type;

   The_PO : PO_Type;
end P;
