package P is

   task type TT (X : Integer);

   protected type PT (X : Integer) is
      procedure Proc;
   private
      Y : Integer := 0;
   end PT;

   procedure PP (X : Integer) with Pre => True;

end P;
