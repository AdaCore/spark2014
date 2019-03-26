with Interfaces.C;

package Test_String with SPARK_Mode => On is
   use Interfaces.C;

   type uint16 is mod 2**16;

   function Get_Result_Text (Code : int) return String;


end Test_String;
