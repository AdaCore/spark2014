package P is

   --  basic protected type with multiple entries
   protected type PT is
      entry E1;
      entry E2;
   private
      G : Boolean := True;
   end;

   --  protected record (here we can statically tell which entry is called)
   type PR is record
      PC1, PC2 : PT;
   end record with Volatile;

   --  protected array (here we cannot statically tell which entry is called)
   type PA is array (Boolean) of PT;

   PO1 : PT;
   PO2 : PR;
   PO3 : PA;

end;
