package body Ada_Main with
   SPARK_Mode
is

   procedure HTTP_Client_Test is

   begin
      Get_Host_By_Name("httpbin.org");
      pragma Assert (False);
   end HTTP_Client_Test;

end Ada_Main;
