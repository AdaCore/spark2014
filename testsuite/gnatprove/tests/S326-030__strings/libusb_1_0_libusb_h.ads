with Interfaces.C; use Interfaces.C;

package libusb_1_0_libusb_h is

   subtype libusb_error is int;
   LIBUSB_ERROR_NO_DEVICE : constant libusb_error := -4;

end libusb_1_0_libusb_h;
