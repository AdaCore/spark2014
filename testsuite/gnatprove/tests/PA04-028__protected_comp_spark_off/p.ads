package P is

   protected type PT is
      procedure Dummy;
      function F return Integer;
   private
      pragma SPARK_Mode (Off);
      X : Integer := PT'Size;   -- this is fine
   end;

end;
