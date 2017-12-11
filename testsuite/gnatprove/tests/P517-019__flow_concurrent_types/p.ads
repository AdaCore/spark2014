package P is
   X : Integer;

   task type T (D : Integer := X);

   protected type PT (D : Integer := X) is
   end PT;

end P;
