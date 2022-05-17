with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   type Int is range 1 .. 10;

   type Int_Record is record
      X : Int := 1;
   end record;

   type Int_Array is array (Int) of Int;

   type Record_Array is array (Int) of Int_Record;

   type Rec is record
     A : Int_Array;
     L : Int;
   end record;

   function Same (I : in Natural) return Natural;

   procedure Old_On_Call (I : in out Natural)
     with
       Pre => I < Integer'Last,
       Post => Same (I)'Old = I - 1;

   procedure Old_On_Record_Field (R : in out Int_Record)
     with
       Pre => R.X < Int'Last,
       Post => R.X = R.X'Old + 1;

   procedure Old_On_Array_Elt (A : in out Int_Array)
     with
       Pre => A(1) < Int'Last,
       Post => A(1) = A(1)'Old + 1;

   procedure Old_On_Record_Field_In_Array (A : in out Record_Array)
     with
       Pre => A(1).X < Int'Last,
       Post => A(1).X = A(1).X'Old + 1;

   procedure Old_On_Integer (I : in out Integer)
     with
       Pre => I < Integer'Last - 1,
       Post => Integer'(I + 1) = Integer'(I + 1)'Old + 1;

   procedure Old_In_Loop_Spec (R : in out Rec)
     with
       Pre => R.A(R.A'First) < Int'Last,
       Post => (for all I in Int range 1 .. R'Old.L => (R.A(I) = R.A(I)));

   --  Implementations

   function Same (I : in Natural) return Natural is (I);

   procedure Old_On_Call (I : in out Natural) is
   begin
      Put_Line ("I before:" & Integer'Image (I));
      I := I + 1;
      Put_Line ("I after: " & Integer'Image (I));
   end Old_On_Call;

   procedure Old_On_Record_Field (R : in out Int_Record) is
   begin
      Put_Line ("Field before:" & Int'Image (R.X));
      R.X := R.X + 1;
      Put_Line ("Field after: " & Int'Image (R.X));
   end Old_On_Record_Field;

   procedure Old_On_Array_Elt (A : in out Int_Array) is
   begin
      Put_Line ("Elt before:" & Int'Image (A (1)));
      A(1) := A(1) + 1;
      Put_Line ("Elt after: " & Int'Image (A (1)));
   end Old_On_Array_Elt;

   procedure Old_On_Record_Field_In_Array (A : in out Record_Array) is
   begin
      Put_Line ("Field before:" & Int'Image (A (1).X));
      A(1).X := A(1).X + 1;
      Put_Line ("Field after:" & Int'Image (A (1).X));
   end Old_On_Record_Field_In_Array;

   procedure Old_On_Integer (I : in out Integer) is
   begin
      Put_Line ("I before:" & Integer'Image (I));
      I := I + 1;
      Put_Line ("I after :" & Integer'Image (I));
   end Old_On_Integer;

   procedure Old_In_Loop_Spec (R : in out Rec) is begin
      Put_Line ("Elt before:" & Int'Image (R.A (R.A'First)));
      null;   --  Do nothing
      Put_Line ("Elt after: " & Int'Image (R.A (R.A'First)));
   end Old_In_Loop_Spec;

   --  Local variables

   I      : Natural := 1;
   J      : Integer := 1;
   Int_R  : Int_Record;
   Rec_A  : Record_Array;
   Int_A1 : Int_Array := (others => 1);
   Int_A2 : Int_Array := (others => 1);
   R      : Rec := (A => Int_A2, L => Int'Last - Int'First);
begin

   Put_Line ("Old_On_Call");
   Old_On_Call (I);
   Put_Line ("");

   Put_Line ("Old_On_Record_Field");
   Old_On_Record_Field (Int_R);
   Put_Line ("");

   Put_Line ("Old_On_Array_Elt");
   Old_On_Array_Elt (Int_A1);
   Put_Line ("");

   Put_Line ("Old_On_Record_Field_In_Array");
   Old_On_Record_Field_In_Array (Rec_A);
   Put_Line ("");

   Put_Line ("Old_On_Integer");
   Old_On_Integer (J);
   Put_Line ("");

   Put_Line ("Old_In_Loop_Spec");
   Old_In_Loop_Spec (R);

end Main;
