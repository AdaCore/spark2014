package P is
   protected type PT is
      procedure Put (X : Integer);
      function Get return Integer;
   private
      Priv : Integer := 0;
   end;

   type Rec is record
      C1, C2 : PT;
   end record with Volatile;

end;
