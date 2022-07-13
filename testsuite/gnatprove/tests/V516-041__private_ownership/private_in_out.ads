package Private_In_Out with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is
   type File_Descriptor is private with
     Default_Initial_Condition => not Is_Open (File_Descriptor),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Open (F : File_Descriptor) return Boolean with
     Global => null,
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");
   function Read_Line (F : File_Descriptor) return String with
     Global => null,
     Pre => Is_Open (F);

   function Open (N : String) return File_Descriptor with
     Global => null,
     Post => Is_Open (Open'Result);
   procedure Close (F : in out File_Descriptor) with
     Global => null,
     Post => not Is_Open (F);

private
   pragma SPARK_Mode (Off);
   type Text;
   type File_Descriptor is access all Text;
end Private_In_Out;
