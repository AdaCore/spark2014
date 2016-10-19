package P is

private
   pragma SPARK_Mode (Off);
   protected type PT is
      function Func return Integer;
   private
      Priv : Integer := Func; --  no error should be generated
   end PT;

end P;
