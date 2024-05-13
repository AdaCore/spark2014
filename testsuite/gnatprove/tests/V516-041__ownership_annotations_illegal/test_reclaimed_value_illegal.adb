
procedure Test_Reclaimed_Value_Illegal with SPARK_Mode is

   package OK_Aspect is
      type Chars_Ptr is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_Ptr : constant Chars_Ptr with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");
   private
      pragma SPARK_Mode (Off);
      type Chars_Ptr is access all Character;

      Null_Ptr : constant Chars_Ptr := null;
   end OK_Aspect;

   package OK_Pragma is
      type Chars_Ptr is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_Ptr : constant Chars_Ptr;
      pragma Annotate (GNATprove, Ownership, "Reclaimed_Value", Null_Ptr);
   private
      pragma SPARK_Mode (Off);
      type Chars_Ptr is access all Character;

      Null_Ptr : constant Chars_Ptr := null;
   end OK_Pragma;

   package No_Name is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_T : constant T with
        Annotate => (GNATprove, Ownership);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;
   end No_Name;

   package Bad_Name is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_T : constant T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Object");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;
   end Bad_Name;

   package Bad_No_Ownership is
      type T is private;

      Null_T : constant T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;
   end Bad_No_Ownership;

   package Bad_No_Reclamation is
      type T is private with
        Annotate => (GNATprove, Ownership);

      Null_T : constant T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;
   end Bad_No_Reclamation;

   package Bad_Tagged is
      type T is tagged private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_T : constant T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");
   private
      pragma SPARK_Mode (Off);
      type Int_Ptr is access Integer;
      type T is tagged record
         X : Int_Ptr;
      end record;

      Null_T : constant T := (X => null);
   end Bad_Tagged;

   package Bad_Duplicated_1 is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_T : constant T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");

      function Is_Null (X : T) return Boolean with
        Annotate => (GNATprove, Ownership, "Is_Reclaimed");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;

      function Is_Null (X : T) return Boolean is (X = null);
   end Bad_Duplicated_1;

   package Bad_Duplicated_2 is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      function Is_Null (X : T) return Boolean with
        Annotate => (GNATprove, Ownership, "Is_Reclaimed");

      Null_T : constant T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;

      function Is_Null (X : T) return Boolean is (X = null);
   end Bad_Duplicated_2;

   package Bad_Location_1 is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      Null_T : constant T;

      function Is_Null (X : T) return Boolean;

      pragma Annotate (GNATprove, Ownership, "Reclaimed_Value", Null_T);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      Null_T : constant T := null;

      function Is_Null (X : T) return Boolean is (X = null);
   end Bad_Location_1;

   package Bad_Location_2 is
      type T is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

         My_Null_T : constant T;
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;

      My_Null_T : constant T := null;
   end Bad_Location_2;

   package Use_Bad_Location_2 is
      use Bad_Location_2;

      Null_T : constant T := My_Null_T with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value");

   end Use_Bad_Location_2;

begin
   null;
end Test_Reclaimed_Value_Illegal;
