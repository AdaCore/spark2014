package P is
   protected type PT is
      procedure Proc;
      function F return Boolean;
   private
      C : Boolean := True;
   end;

   PO : PT;
end;
