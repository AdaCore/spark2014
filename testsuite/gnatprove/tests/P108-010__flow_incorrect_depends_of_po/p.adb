package body P is
   protected body PO_Type is
      procedure Set (X : Integer) is
      begin
         Content := X;
      end Set;

      function Get return Integer is (Content);
   end PO_Type;
end P;
