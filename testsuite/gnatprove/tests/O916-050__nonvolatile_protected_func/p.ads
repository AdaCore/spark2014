package P with SPARK_Mode is

   protected type PT is
      procedure Proc;
      function F return Boolean;
   end;

   protected Other is
      function G return Boolean;
   end;

end;
