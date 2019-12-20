with Ada.Containers.Functional_Vectors;
with Ada.Containers; use Ada.Containers;

generic
   type Element_Type (<>) is private;
   type Element_Model (<>) is private;
   with function Model (X : Element_Type) return Element_Model is <>;
   with function Copy (X : Element_Type) return Element_Type is <>;
package Formal_Vectors with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Vector is private;

   function Length (V : Vector) return Natural;

   procedure Append (V : in out Vector; E : Element_Type) with
     Pre  => Length (V) < Positive'Last,
     Post => Length (V) = Length (V)'Old + 1
         and then Element (V, Length (V)) = E
         and then Model (V)'Old <= Model (V);
   procedure Append (V : in out Vector; E : in out Vector) with
     Pre  => Length (V) < Positive'Last - Length (E),
     Post =>  Length (V) = Length (V)'Old + Length (E)'Old
         and then Length (E) = 0
         and then Model (V)'Old <= Model (V)
         and then Range_Shifted (Model (E)'Old, Model (V), 1, Length (E)'Old, Count_Type (Length (V)'Old));
   procedure Insert (V : in out Vector;  I : Positive; E : Element_Type) with
     Pre  => Length (V) < Positive'Last and then I in 1 .. Length (V) + 1;
  --   Post => Model (V) = Model (V)'Old (1 .. I - 1) & E & Model (V)'Old (I .. Length (V)'Old);
   procedure Replace (V : in out Vector; I : Positive; E : Element_Type) with
     Pre  => I in 1 .. Length (V);
  --   Post => Model (V) = Model (V)'Old'Update (I => E);
   procedure Delete_Last (V : in out Vector); -- with
   --  Post => (if Length (V)'Old = 0 then Model (V) = Model (V)'Old
      --        else Model (V) = Model (V)'Old (1 .. Length (V)'Old - 1));
   procedure Delete (V : in out Vector; I : Positive) with
     Pre  => I in 1 .. Length (V);
    -- Post => (if Length (V)'Old = 0 then Model (V) = Model (V)'Old
             -- elsif I = Length (V)'Old then Model (V) = Model (V)'Old (1 .. I - 1)
            --  else Model (V) = Model (V)'Old (1 .. I - 1) & Model (V)'Old (I + 1 .. Length (V)'Old));

   function Element (V : Vector; I : Positive) return Element_Type with
     Pre => I in 1 .. Length (V),
     Post => Model (Element'Result) = Get (Model (V), I);

   -- function Element (V : Vector; I : Positive) return access Element_Type; --  traversal functions on ownership types not supported by RM yet

   package Model_Sequence is new Ada.Containers.Functional_Vectors (Positive, Element_Model);
   use all type Model_Sequence.Sequence;
   subtype Model_Type is Model_Sequence.Sequence;

   function Model (V : Vector) return Model_Type with Ghost,
     Post => Last (Model'Result) = Length (V);

private
   type Element_Access is access Element_Type;
   type Element_Array is array (Positive range <>) of Element_Access; --with
     --Predicate => Element_Array'First = 1;
   type Element_Array_Access is access Element_Array;
   type Vector is record
      Top     : Natural := 0;
      Content : Element_Array_Access;
   end record with
     Predicate =>
       (Top = 0 or else
          (Content /= null and then Content.all'Last >= Top
           and then
             (for all I in 1 .. Top => Content.all (I) /= null)));

   function Length (V : Vector) return Natural is
     (V.Top);
end Formal_Vectors;
