with SPARK.Pointers.Poisoned.Pointers;

--  A vector whose element cells are poisoned holders.
--
--  Element storage is abstracted behind a formal Holder_Type plus six
--  operations -- Set_Element, Constant_Access, Is_Initialized, Is_Reclaimed,
--  Move, Needs_Reclamation -- and the bulk moves behind three more formal
--  procedures, Relocate, Relocate_And_Fill and Relocate_And_Copy, because the
--  shared code has to state the move-and-reclaim discipline itself.
--
--  SPARK.Pointers.Poisoned.Pointers supplies all of that: the discipline lives
--  in the type's own contract, and Array_Operations.Relocate is the bulk move
--  with its contract already written.
--
--  Make_Hole below is the point of the exercise. The prototype fuses the slide
--  with the fill (Relocate_And_Fill) for one reason: without poisoned values a
--  subprogram may not return with a moved-out parameter, so a standalone slide
--  could not return. A poisoned cell is a legal moved-from value, so Make_Hole
--  returns with the hole open and the fill is ordinary code in its caller. The
--  fused operation is not needed.

procedure Poisoned_Vector with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   --  Required to instantiate Pointers.Array_Operations: its contracts use
   --  Copy (A)'Old under quantifiers.

   Capacity : constant := 100;

   type Index_Type is range 1 .. Capacity;
   subtype Extended_Index is Index_Type'Base range 0 .. Capacity;

   type Element_Type is record
      Key : Integer;
      Val : Integer;
   end record;

   function Is_Reclaimed (Unused : Element_Type) return Boolean is (True)
   with Ghost => Static, Global => null;

   package Cells is new
     SPARK.Pointers.Poisoned.Pointers (Element_Type, Is_Reclaimed);
   use Cells;

   package Arrays is new Cells.Array_Operations (Index_Type);
   use Arrays;

   function Id (E : Element_Type) return Element_Type is (E)
   with Global => null;
   package Values is new Cells.Copy_Operations (Id);
   use Values;

   type Vector is record
      Elements : Pointer_Array (1 .. Capacity);
      Last     : Extended_Index;
   end record;

   --  The structural invariant

   function Valid_Elements (V : Vector) return Boolean
   is (for all I in Index_Type =>
         (if I <= V.Last
          then
            not Is_Poisoned (V.Elements (I))
            and then V.Elements (I) /= Null_Pointer
          else Is_Reclaimed (V.Elements (I))))
   with Ghost => Static, Global => null;
   --  A cell in use designates an element, so it is neither poisoned nor
   --  null. A cell past Last is reclaimed, that is, poisoned or null.

   function Hole_At (V : Vector; Hole : Index_Type) return Boolean
   is (for all I in Index_Type =>
         (if I = Hole or else I > V.Last
          then Is_Reclaimed (V.Elements (I))
          else
            not Is_Poisoned (V.Elements (I))
            and then V.Elements (I) /= Null_Pointer))
   with Ghost => Static, Global => null;
   --  Valid_Elements, except that one cell inside the used range is poisoned.
   --  A state the prototype's design cannot let a subprogram return in.

   function Element (V : Vector; I : Index_Type) return Element_Type
   with
     Global => null,
     Pre    => Valid_Elements (V) and then I <= V.Last,
     Post   =>
       (Static => Object_Logic_Equal (Element'Result, Peek (V.Elements (I))));

   procedure Make_Hole (V : in out Vector; Before : Index_Type)
   with
     Global => null,
     Pre    =>
       Valid_Elements (V)
       and then V.Last < Capacity
       and then Before <= V.Last + 1,
     Post   =>
       V.Last = V.Last'Old + 1
       and then Hole_At (V, Before)
       and then (for all I in Index_Type =>
                   (if I < Before
                    then Extensional_Eq (V.Elements (I), Copy (V.Elements)'Old (I))))
       and then (for all I in Index_Type =>
                   (if I > Before and I <= V.Last
                    then Extensional_Eq
                           (V.Elements (I), Copy (V.Elements)'Old (I - 1))));

   procedure Replace_Element
     (V : in out Vector; I : Index_Type; E : Element_Type)
   with
     Global => null,
     Pre    => Valid_Elements (V) and then I <= V.Last,
     Post   =>
       Valid_Elements (V)
       and then V.Last = V.Last'Old
       and then Object_Logic_Equal (Peek (V.Elements (I)), E);

   procedure Delete (V : in out Vector; Index : Index_Type)
   with
     Global => null,
     Pre    => Valid_Elements (V) and then Index <= V.Last,
     Post   => Valid_Elements (V) and then V.Last = V.Last'Old - 1;

   procedure Insert (V : in out Vector; Before : Index_Type; E : Element_Type)
   with
     Global => null,
     Pre    =>
       Valid_Elements (V)
       and then V.Last < Capacity
       and then Before <= V.Last + 1,
     Post   =>
       Valid_Elements (V)
       and then V.Last = V.Last'Old + 1
       and then Object_Logic_Equal (Peek (V.Elements (Before)), E)
       --  The elements before the insertion point are untouched, and those
       --  from it on have shifted up one place.
       and then (for all I in Index_Type =>
                   (if I < Before
                    then Extensional_Eq (V.Elements (I), Copy (V.Elements)'Old (I))))
       and then (for all I in Index_Type =>
                   (if I > Before and I <= V.Last
                    then Extensional_Eq
                           (V.Elements (I), Copy (V.Elements)'Old (I - 1))));

   procedure Clear (V : in out Vector)
   with
     Global => null,
     Pre    => Valid_Elements (V),
     Post   => Valid_Elements (V) and then V.Last = 0;

   -------------
   -- Bodies  --
   -------------

   function Element (V : Vector; I : Index_Type) return Element_Type
   is (Deref (V.Elements (I)));

   procedure Make_Hole (V : in out Vector; Before : Index_Type) is
   begin
      Relocate
        (V.Elements,
         Source_From  => Before,
         Source_Up_To => V.Last,
         Target_From  => Before + 1,
         Target_Up_To => V.Last + 1);

      V.Last := V.Last + 1;
   end Make_Hole;

   procedure Insert (V : in out Vector; Before : Index_Type; E : Element_Type)
   is
   begin
      Make_Hole (V, Before);
      --  The hole is poisoned, so it owns nothing and may be overwritten.
      V.Elements (Before) := Create_Copy (E);
   end Insert;

   procedure Replace_Element
     (V : in out Vector; I : Index_Type; E : Element_Type) is
   begin
      Assign (V.Elements (I), E);
   end Replace_Element;

   procedure Delete (V : in out Vector; Index : Index_Type) is
   begin
      --  Reclaim first: Relocate needs its landing cell to own nothing.
      Reclaim (V.Elements (Index));

      --  A relocation with no fill -- the case Relocate_And_Fill cannot serve.
      Relocate
        (V.Elements,
         Source_From  => Index + 1,
         Source_Up_To => V.Last,
         Target_From  => Index,
         Target_Up_To => V.Last - 1);

      V.Last := V.Last - 1;
   end Delete;

   procedure Clear (V : in out Vector) is
   begin
      for I in 1 .. V.Last loop
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if J in I .. V.Last
               then not Is_Poisoned (V.Elements (J))
               else Is_Reclaimed (V.Elements (J))));
         Reclaim (V.Elements (I));
      end loop;
      V.Last := 0;
   end Clear;

begin
   null;
end Poisoned_Vector;
