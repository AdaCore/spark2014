procedure Test with SPARK_Mode is

   --  Aspect Unhide_Info for package bodies shall be on a package body

   package Bad_1 with
      Annotate => (GNATprove, Unhide_Info, "Package_Body")
   is
      function Id (X : Integer) return Integer is (X);
   end Bad_1;

   --  Pragma Unhide_Info for package bodies shall have 3 parameters

   package Bad_2 is
      function Id (X : Integer) return Integer;
   end Bad_2;

   package body Bad_2 is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body", Bad_2);
      function Id (X : Integer) return Integer is (X);
   end Bad_2;

   --  Pragma Unhide_Info for package bodies shall be located at the top of the package body

   package Bad_3 is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");
      function Id (X : Integer) return Integer;
   end Bad_3;

   package body Bad_3 is
      function Id (X : Integer) return Integer is (X);
   end Bad_3;

   package Bad_4 is
      function Id (X : Integer) return Integer;
   end Bad_4;

   package body Bad_4 is
      function Id (X : Integer) return Integer is (X);
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");
   end Bad_4;

   package Bad_5 is
      function Id (X : Integer) return Integer;
   end Bad_5;

   package body Bad_5 is
      function Id (X : Integer) return Integer is
      begin
        pragma Annotate (GNATprove, Unhide_Info, "Package_Body");
	return X;
      end Id;
   end Bad_5;

   --  Hide_Info cannot be applied to package bodies

   package Bad_6 is
      function Id (X : Integer) return Integer;
   end Bad_6;

   package body Bad_6 with
      Annotate => (GNATprove, Hide_Info, "Package_Body")
   is
      function Id (X : Integer) return Integer is (X);
   end Bad_6;

   --  Both pragma and aspect forms are accepted

   package OK_1 is
      function Id (X : Integer) return Integer;
   end OK_1;

   package body OK_1 with
      Annotate => (GNATprove, Unhide_Info, "Package_Body")
   is
      function Id (X : Integer) return Integer is (X);
   end OK_1;

   package OK_2 is
      function Id (X : Integer) return Integer;
   end OK_2;

   package body OK_2 is
      pragma Annotate (GNATprove, Unhide_Info, "Package_Body");
      function Id (X : Integer) return Integer is (X);
   end OK_2;

begin
   null;
end Test;
