procedure Proc with
  SPARK_Mode
is
   procedure Orig is
   begin
      null;
   end Orig;

   package Wrapper is
      procedure Proxy;
   private
      procedure Proxy renames Orig;
   end Wrapper;
begin
   Wrapper.Proxy;
end Proc;
