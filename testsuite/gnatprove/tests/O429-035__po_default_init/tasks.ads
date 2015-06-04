package Tasks is

   X : Integer;

   protected type Store
   is
   private
      Variable_Integer : Integer := X;
   end Store;

end Tasks;
