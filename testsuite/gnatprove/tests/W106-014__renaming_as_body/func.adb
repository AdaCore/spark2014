function Func return Natural with
  SPARK_Mode
is
   function Orig return Natural is
   begin
      return 0;
   end Orig;

   package Wrapper is
      function Proxy return Natural;
   private
      function Proxy return Natural renames Orig;
   end Wrapper;
begin
   return Wrapper.Proxy;
end Func;
