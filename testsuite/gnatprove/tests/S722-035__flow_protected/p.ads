package P is
   protected type PT is
      procedure Proc;
      function Fun return Boolean;
   private
      Comp : Boolean := True;
   end PT;
end P;
