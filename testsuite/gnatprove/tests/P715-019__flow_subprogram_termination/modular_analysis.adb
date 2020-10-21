with File_IO;  -- This package is in SPARK but does not have a body

package body Modular_Analysis is

   procedure Test_01 (F : out File_IO.File) with Annotate => (GNATprove, Terminating)
   is
   begin
      File_IO.Open_Read ("foobar.so", F);
   end Test_01;

end Modular_Analysis;
