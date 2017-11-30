package P is

   protected PO is
      procedure Proc;
      function Fun return Integer;
   private
      X : Integer := 0;
   end;

   protected type PT is
      procedure Proc;
      function Fun return Integer;
   private
      X : Integer := 0;
   end;

   function  Fun  (X : Integer) return Integer;
   procedure Proc (X : in out Integer);

end;
