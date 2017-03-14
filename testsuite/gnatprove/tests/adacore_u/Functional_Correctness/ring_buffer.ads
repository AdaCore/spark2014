with Ada.Containers; use Ada.Containers;
with Ada.Containers.Functional_Vectors;

package Ring_Buffer with SPARK_Mode is
   Max_Size : constant Natural := 100;
   subtype Length_Range is Integer range 0 .. Max_Size;
   subtype Index_Type is Integer range 1 .. Max_Size;
   package My_Seq is new Ada.Containers.Functional_Vectors
     (Index_Type   => Index_Type,
      Element_Type => Natural);
   use My_Seq;

   function Is_Append (S1, S2 : Sequence; E : Natural) return Boolean is
      (S1 < S2 and then Length (S1) = Length (S2) - 1
        and then Get (S2, Last (S2)) = E)
   with Ghost;
   function Is_Prepend (S1, S2 : Sequence; E : Natural) return Boolean is
      (Length (S1) = Length (S2) - 1
        and then Get (S2, 1) = E
        and then
          (for all I in 1 .. Last (S1) => Get (S1, I) = Get (S2, I + 1)))
   with Ghost;

   subtype Model_Type is Sequence with Ghost;
   Model : Model_Type with Ghost;

   function Valid_Model return Boolean with Ghost;
   function Valid_Model (M : Model_Type) return Boolean with Ghost;

   function Get_Model return Model_Type with Ghost,
     Post => Valid_Model (Get_Model'Result);

   procedure Push_Last1 (E : Natural) with
     Pre  => Length_Range (Length (Get_Model)) < Max_Size,
     Post => Is_Append (Get_Model'Old, Get_Model, E);

   procedure Push_Last (E : Natural) with
     Pre  => Valid_Model and Length_Range (Length (Model)) < Max_Size,
     Post => Valid_Model and Is_Append (Model'Old, Model, E);

   procedure Pop_First (E : out Natural) with
     Pre  => Valid_Model and Length (Model) > 0,
     Post => Valid_Model and Is_Prepend (Model, Model'Old, E);

   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Pop_When_Available (E : in out Natural) with
     Pre            => Valid_Model,
     Post           => Valid_Model,
     Contract_Cases =>
     (Length (Model) > 0 => Is_Prepend (Model, Model'Old, E),
      others             => Model = Model'Old and E = E'Old);
end Ring_Buffer;
