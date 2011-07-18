pragma Source_File_Name (ada_main, Spec_File_Name => "b_gnatb.ads");
pragma Source_File_Name (ada_main, Body_File_Name => "b_gnatb.adb");

package body ada_main is

   procedure adainit is
   begin
      System.Soft_Links'Elab_Spec;
   end adainit;

end ada_main;
