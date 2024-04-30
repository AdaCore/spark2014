procedure RFC_Vectors_Example is

   generic
      type Elem_Type is private;
   package Vectors is

       type Vector is private;

       procedure Add_Element (V : in out Vector; Elem : Elem_Type);

       function Nth_Element (V : Vector; N : Positive) return Elem_Type;

       function Length (V : Vector) return Natural;

   private

       function Capacity (V : Vector) return Natural;
          --  Return number of elements that may be added without causing
          --  any new allocation of space

       type Vector is array (1 .. 100) of Integer;
       --  with Type_Invariant => Vector.Length <= Vector.Capacity;

   end Vectors;

   package body Vectors is

       E : Elem_Type;

       procedure Add_Element (V : in out Vector; Elem : Elem_Type) is
       begin
          null;
       end Add_Element;

       function Nth_Element (V : Vector; N : Positive) return Elem_Type is
       begin
          return E;
       end Nth_Element;

       function Length (V : Vector) return Natural is
       begin
          return 0;
       end Length;

       function Capacity (V : Vector) return Natural is
       begin
          return 100;
       end Capacity;

   end Vectors;

   package Int_Vecs is new Vectors(Integer);

   V : Int_Vecs.Vector;

begin
   V.Add_Element(42);
   V.Add_Element(-33);
   pragma Assert (V.Length = 2);
   pragma Assert (V.Nth_Element(1) = 42);
end RFC_Vectors_Example;
