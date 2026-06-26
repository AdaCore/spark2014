pragma Ada_2022;

with SPARK.Containers.Types; use SPARK.Containers.Types;

generic
   type Index_Type is range <>;
   type Element_Type is private;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;
package SPARK.Containers.Formal.Impl.Vectors with
  SPARK_Mode,
  Always_Terminates
is
   subtype Extended_Index is
     Index_Type'Base
       range Index_Type'Pred (Index_Type'First) .. Index_Type'Last;

   No_Index : constant Extended_Index := Extended_Index'First;

   Last_Count : constant Count_Type :=
     (if Index_Type'Last < Index_Type'First
      then 0
      elsif Index_Type'Last < -1
        or else
          Index_Type'Pos (Index_Type'First)
          > Index_Type'Pos (Index_Type'Last) - Count_Type'Last
      then
        Index_Type'Pos (Index_Type'Last)
        - Index_Type'Pos (Index_Type'First)
        + 1
      else Count_Type'Last);
   --  Maximal capacity of any vector. It is the minimum of the size of the
   --  index range and the last possible Count_Type.

   subtype Capacity_Range is Count_Type range 0 .. Last_Count;

   type Vector (Capacity : Capacity_Range) is private;

   pragma Unevaluated_Use_Of_Old (Allow);

   function First_Index (Container : Vector) return Index_Type
   with Global => null;

   function Last_Index (Container : Vector) return Extended_Index
   with Global => null;

   function Length (Container : Vector) return Capacity_Range
   with Global => null;

   procedure Delete (Container : in out Vector; Index : Extended_Index)
   with
     Global     => null,
     Exit_Cases =>
       (Index < First_Index (Container)
        or else Index - 1 > Last_Index (Container) =>
          (Exception_Raised => Constraint_Error),
        others => Normal_Return);

   procedure Delete
     (Container : in out Vector; Index : Extended_Index; Count : Count_Type)
   with
     Global     => null,
     Exit_Cases =>
       (Index < First_Index (Container)
        or else Index - 1 > Last_Index (Container) =>
          (Exception_Raised => Constraint_Error),
        others => Normal_Return);

private

   type Relaxed_Element is record
      V : aliased Element_Type;
   end record
   with Relaxed_Initialization;

   subtype Array_Index is Capacity_Range range 1 .. Capacity_Range'Last;
   type Elements_Array is array (Array_Index range <>) of Relaxed_Element;

   function "=" (L, R : Elements_Array) return Boolean is abstract;

   function Used_Length (Last : Extended_Index) return Capacity_Range
   is (Capacity_Range
         (Long_Long_Integer (Last) - Long_Long_Integer (No_Index)));
   --  Number of used cells for a given Last. Takes Last (not a Vector) so it
   --  can appear in the structural predicate below without triggering a
   --  predicate-check recursion.

   type Vector (Capacity : Capacity_Range) is record
      Last     : Extended_Index := No_Index;
      Elements : Elements_Array (1 .. Capacity);
   end record;

   function Length (Container : Vector) return Capacity_Range
   is (Used_Length (Container.Last));

   function First_Index (Container : Vector) return Index_Type
   is (Index_Type'First);

   function Last_Index (Container : Vector) return Extended_Index
   is (Container.Last);

end SPARK.Containers.Formal.Impl.Vectors;
