package body Aida.Containers.Formal_Vectors is
   pragma SPARK_Mode;

   function Empty_Vector return Vector_Type is
   begin
      return V : Vector_Type := (Capacity      => Vector_Type_Owner.Empty_Vector.Capacity,
                                 Hidden_Vector => Vector_Type_Owner.Empty_Vector)
      do
         null;
      end return;
   end Empty_Vector;

   function "=" (Left, Right : Vector_Type)
                 return Boolean is
   begin
      return Vector_Type_Owner."=" (Left.Hidden_Vector, Right.Hidden_Vector);
   end "=";

   function To_Vector (New_Item : Element_Type;
                       Length   : Capacity_Range)
                       return Vector_Type is
   begin
      return V : Vector_Type := (Capacity      => Length,
                                 Hidden_Vector => Vector_Type_Owner.To_Vector (New_Item => New_Item,
                                                                               Length   => Length))
      do
         null;
      end return;
   end To_Vector;

   function Capacity (Container : Vector_Type)
                      return Capacity_Range
   is
   begin
      return Container.Capacity;
   end Capacity;

   procedure Reserve_Capacity (Container : in out Vector_Type;
                               Capacity  : Capacity_Range)
   is
   begin
      Vector_Type_Owner.Reserve_Capacity (Container.Hidden_Vector, Capacity);
   end Reserve_Capacity;

   function Length (Container : Vector_Type)
                    return Capacity_Range is
   begin
      return Vector_Type_Owner.Length (Container.Hidden_Vector);
   end Length;

   function Is_Empty (Container : Vector_Type'Class)
                      return Boolean is
   begin
      return Vector_Type_Owner.Is_Empty (Container.Hidden_Vector);
   end Is_Empty;

   procedure Clear (Container : in out Vector_Type) is
   begin
      Vector_Type_Owner.Clear (Container.Hidden_Vector);
   end Clear;

   procedure Assign (Target : in out Vector_Type;
                     Source : Vector_Type) is
   begin
      Vector_Type_Owner.Assign (Target.Hidden_Vector, Source.Hidden_Vector);
   end Assign;

   function Copy (Source   : Vector_Type;
                  Capacity : Capacity_Range := 0)
                  return Vector_Type is
   begin
      return V : Vector_Type := (Capacity      => Capacity,
                                 Hidden_Vector => Vector_Type_Owner.Copy (Source.Hidden_Vector, Capacity))
      do
         null;
      end return;
   end Copy;

   function Element (Container : Vector_Type;
                     Index     : Index_Type)
                     return Element_Type
   is
   begin
      return Vector_Type_Owner.Element (Container.Hidden_Vector, Index);
   end Element;

   procedure Replace_Element (Container : in out Vector_Type;
                              Index     : Index_Type;
                              New_Item  : Element_Type) is
   begin
      Vector_Type_Owner.Replace_Element (Container.Hidden_Vector,
                                         Index,
                                         New_Item);
   end Replace_Element;

   procedure Append (Container : in out Vector_Type;
                     New_Item  : Vector_Type) is
   begin
      Vector_Type_Owner.Append (Container.Hidden_Vector,
                                New_Item.Hidden_Vector);
   end Append;

   procedure Append (Container : in out Vector_Type;
                     New_Item  : Element_Type) is
   begin
      Vector_Type_Owner.Append (Container.Hidden_Vector,
                                New_Item);
   end Append;

   procedure Delete_Last (Container : in out Vector_Type) is
   begin
      Vector_Type_Owner.Delete_Last (Container.Hidden_Vector);
   end Delete_Last;

   procedure Reverse_Elements (Container : in out Vector_Type) is
   begin
      Vector_Type_Owner.Reverse_Elements (Container.Hidden_Vector);
   end Reverse_Elements;

   procedure Swap (Container : in out Vector_Type;
                   I, J : Index_Type) is
   begin
      Vector_Type_Owner.Swap (Container.Hidden_Vector, I, J);
   end Swap;

   function First_Index (Container : Vector_Type)
                         return Index_Type is
   begin
      return Vector_Type_Owner.First_Index (Container.Hidden_Vector);
   end First_Index;

   function First_Element (Container : Vector_Type) return Element_Type is
   begin
      return Vector_Type_Owner.First_Element (Container.Hidden_Vector);
   end First_Element;

   function Last_Index (Container : Vector_Type) return Extended_Index is
   begin
      return Vector_Type_Owner.Last_Index (Container.Hidden_Vector);
   end Last_Index;

   function Last_Element (Container : Vector_Type) return Element_Type is
   begin
      return Vector_Type_Owner.Last_Element (Container.Hidden_Vector);
   end Last_Element;

   function Find_Index (Container : Vector_Type;
                        Item      : Element_Type;
                        Index     : Index_Type := Index_Type'First)
                        return Extended_Index is
   begin
      return Vector_Type_Owner.Find_Index (Container.Hidden_Vector,
                                           Item,
                                           Index);
   end Find_Index;

   function Reverse_Find_Index (Container : Vector_Type;
                                Item      : Element_Type;
                                Index     : Index_Type := Index_Type'Last)
                                return Extended_Index is
   begin
      return Vector_Type_Owner.Reverse_Find_Index (Container.Hidden_Vector,
                                                   Item,
                                                   Index);
   end Reverse_Find_Index;

   function Contains (Container : Vector_Type;
                      Item      : Element_Type)
                      return Boolean is
   begin
      return Vector_Type_Owner.Contains (Container.Hidden_Vector,
                                         Item);
   end Contains;

   function Has_Element (Container : Vector_Type;
                         Position  : Extended_Index)
                         return Boolean is
   begin
      return Vector_Type_Owner.Has_Element (Container.Hidden_Vector,
                                            Position);
   end Has_Element;

   package body Generic_Sorting is

      package Sorting_Package is new Vector_Type_Owner.Generic_Sorting ("<");

      function Is_Sorted (Container : Vector_Type)
                          return Boolean is
      begin
         return Sorting_Package.Is_Sorted (Container.Hidden_Vector);
      end Is_Sorted;

      procedure Sort (Container : in out Vector_Type) is
      begin
         Sorting_Package.Sort (Container.Hidden_Vector);
      end Sort;

   end Generic_Sorting;

end Aida.Containers.Formal_Vectors;
