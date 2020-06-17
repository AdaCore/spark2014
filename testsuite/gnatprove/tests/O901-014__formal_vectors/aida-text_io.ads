package Aida.Text_IO is
   pragma SPARK_Mode;

   -- Wrapper around Ada.Test_IO.Put_Line.
   -- If one uses Ada.Text_IO.Put_Line directly one will get Warning from GNATprove
   -- that Put_Line lacks a global aspect.
   procedure Put_Line (Item : String) with
     Global => null;

end Aida.Text_IO;
