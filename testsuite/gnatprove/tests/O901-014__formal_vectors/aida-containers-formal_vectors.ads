with Ada.Containers.Formal_Indefinite_Vectors;

generic
   type Index_Type is range <>;
   type Element_Type is private;

   with function "=" (Left, Right : Element_Type) return Boolean is <>;

   Bounded : Boolean := True;
   --  If True, the containers are bounded; the initial capacity is the maximum
   --  size, and heap allocation will be avoided. If False, the containers can
   --  grow via heap allocation.
package Aida.Containers.Formal_Vectors is
   pragma SPARK_Mode;

   use type Ada.Containers.Count_Type;

   subtype Extended_Index is Index_Type'Base range Index_Type'First - 1 .. Index_Type'Min (Index_Type'Base'Last - 1, Index_Type'Last) + 1;

   No_Index : constant Extended_Index := Extended_Index'First;

   subtype Capacity_Range is Ada.Containers.Count_Type range 0 .. Ada.Containers.Count_Type (Index_Type'Last - Index_Type'First + 1);

   type Vector_Type (Capacity : Capacity_Range) is tagged limited private with
     Default_Initial_Condition => Is_Empty (Vector_Type);
   --  In the bounded case, Capacity is the capacity of the container, which
   --  never changes. In the unbounded case, Capacity is the initial capacity
   --  of the container, and operations such as Reserve_Capacity and Append can
   --  increase the capacity. The capacity never shrinks, except in the case of
   --  Clear.
   --
   --  Note that all objects of type Vector are constrained, including in the
   --  unbounded case; you can't assign from one object to another if the
   --  Capacity is different.

   function Empty_Vector return Vector_Type;

   function "=" (Left, Right : Vector_Type) return Boolean with
     Global => null;

   function To_Vector
     (New_Item : Element_Type;
      Length   : Capacity_Range) return Vector_Type
   with
     Global => null;

   function Capacity (Container : Vector_Type) return Capacity_Range with
     Global => null,
     Post'Class => Capacity'Result >= Container.Capacity;

   procedure Reserve_Capacity
     (Container : in out Vector_Type;
      Capacity  : Capacity_Range)
   with
     Global => null,
     Pre'Class => (if Bounded then Capacity <= Container.Capacity);

   function Length (Container : Vector_Type) return Capacity_Range with
     Global => null;

   function Is_Empty (Container : Vector_Type'Class) return Boolean with
     Global => null;

   procedure Clear (Container : in out Vector_Type) with
     Global => null;
   --  Note that this reclaims storage in the unbounded case. You need to call
   --  this before a container goes out of scope in order to avoid storage
   --  leaks. In addition, "X := ..." can leak unless you Clear(X) first.

   procedure Assign (Target : in out Vector_Type; Source : Vector_Type) with
     Global => null,
     Pre'Class => (if Bounded then Length (Source) <= Target.Capacity);

   function Copy
     (Source   : Vector_Type;
      Capacity : Capacity_Range := 0) return Vector_Type
   with
     Global => null,
     Pre'Class    => (if Bounded then (Capacity = 0 or Length (Source) <= Capacity));

   function Element (Container : Vector_Type;
                     Index     : Index_Type) return Element_Type
     with
       Global => null,
       Pre'Class    => Index in First_Index (Container) .. Last_Index (Container);

   procedure Replace_Element
     (Container : in out Vector_Type;
      Index     : Index_Type;
      New_Item  : Element_Type)
   with
     Global => null,
     Pre'Class    => Index in First_Index (Container) .. Last_Index (Container);

   procedure Append
     (Container : in out Vector_Type;
      New_Item  : Vector_Type)
   with
     Global => null,
     Pre'Class    => (if Bounded then
                 Length (Container) + Length (New_Item) <= Container.Capacity);

   procedure Append
     (Container : in out Vector_Type;
      New_Item  : Element_Type)
   with
     Global => null,
     Pre'Class    => (if Bounded then
                  Length (Container) < Container.Capacity);

   procedure Delete_Last
     (Container : in out Vector_Type)
   with
     Global => null;

   procedure Reverse_Elements (Container : in out Vector_Type) with
     Global => null;

   procedure Swap (Container : in out Vector_Type; I, J : Index_Type) with
     Global => null,
     Pre'Class    => I in First_Index (Container) .. Last_Index (Container)
     and then J in First_Index (Container) .. Last_Index (Container);

   function First_Index (Container : Vector_Type) return Index_Type with
     Global => null;

   function First_Element (Container : Vector_Type) return Element_Type with
     Global => null,
     Pre'Class    => not Is_Empty (Container);

   function Last_Index (Container : Vector_Type) return Extended_Index with
     Global => null;

   function Last_Element (Container : Vector_Type) return Element_Type with
     Global => null,
     Pre'Class    => not Is_Empty (Container);

   function Find_Index
     (Container : Vector_Type;
      Item      : Element_Type;
      Index     : Index_Type := Index_Type'First) return Extended_Index
   with
     Global => null;

   function Reverse_Find_Index
     (Container : Vector_Type;
      Item      : Element_Type;
      Index     : Index_Type := Index_Type'Last) return Extended_Index
   with
     Global => null;

   function Contains
     (Container : Vector_Type;
      Item      : Element_Type) return Boolean
   with
     Global => null;

   function Has_Element
     (Container : Vector_Type;
      Position  : Extended_Index) return Boolean
   with
     Global => null;

   generic
      with function "<" (Left, Right : Element_Type) return Boolean is <>;
   package Generic_Sorting is

      function Is_Sorted (Container : Vector_Type) return Boolean with
        Global => null;

      procedure Sort (Container : in out Vector_Type) with
        Global => null;

   end Generic_Sorting;

private

   package Vector_Type_Owner is new Ada.Containers.Formal_Indefinite_Vectors (Index_Type   => Index_Type,
                                                                              Element_Type => Element_Type,
                                                                              Bounded      => Bounded,
                                                                              Max_Size_In_Storage_Elements => Element_Type'Size);

   type Vector_Type (Capacity : Capacity_Range) is tagged limited
      record
         Hidden_Vector : Vector_Type_Owner.Vector (Capacity);
      end record;

end Aida.Containers.Formal_Vectors;
