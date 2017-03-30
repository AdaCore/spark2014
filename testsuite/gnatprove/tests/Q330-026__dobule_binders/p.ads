package P is

   protected type PT is
      function Prot return Boolean;
   private
      Dummy : Boolean := True;
   end;

end;
