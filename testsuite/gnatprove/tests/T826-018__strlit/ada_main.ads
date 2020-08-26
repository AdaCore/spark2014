with Interfaces.C; use Interfaces.C;

package Ada_Main with
   SPARK_Mode
is

   procedure Get_Host_By_Name (Server_Name : char_array)
      with
        Import => True;

   procedure HTTP_Client_Test;

end Ada_Main;
