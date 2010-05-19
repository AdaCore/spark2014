-- FPGA interface
--
-- $Log: fpga.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/13 15:35:32  adi
-- Initial revision
--
--

package Fpga
is

   -- Base address for input to FPGA
   Base_In_Address  : constant := 16#8000_0000#;

   -- Base address for output to FPGA
   Base_Out_Address : constant := 16#8000_1000#;

end Fpga;
