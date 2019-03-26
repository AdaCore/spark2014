with libusb_1_0_libusb_h;
package body Test_String with SPARK_Mode => On is

   use libusb_1_0_libusb_h;
   function Get_Result_Text (Code : int) return String is
   begin
      case Code is
         when LIBUSB_ERROR_NO_DEVICE =>
            return "USB Error: No device";
         when others =>
            return "Unknown error";
      end case;
   end Get_Result_Text;



end Test_String;
