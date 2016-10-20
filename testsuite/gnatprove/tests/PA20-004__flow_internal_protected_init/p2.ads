package P2 is

   protected type PT is
      function Func return Integer;
   private
      Priv : Integer := PT.Func;
   end PT;

end;
