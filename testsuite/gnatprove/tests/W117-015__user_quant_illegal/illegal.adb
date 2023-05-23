
procedure Illegal with SPARK_Mode is

   package Iterable_Reading_Globals is

      --  Iterable primitives that depends on globals
      --    are disallowed in SPARK; there should be
      --    an error message for every single primitive.

      Global_Flag : Boolean := True;

      type Container_Globals is (Iter)
        with Iterable => (First       => First,
                          Next        => Next,
                          Last        => First,
                          Previous    => Next,
                          Has_Element => Has_Element,
                          Element     => Element);

      function First (C : Container_Globals) return Integer is
        (if Global_Flag then 1 else 0);
      function Next (C : Container_Globals; X : Integer) return Integer is
        (if Global_Flag then 1 else 0);
      function Has_element (C : Container_Globals; X : Integer) return Boolean is
        (Global_Flag and then X = 0);
      function Element (C : Container_Globals; X : Integer) return Integer is
        (if Global_Flag then X else 0);
   end Iterable_Reading_Globals;

   package Iterable_And_Privacy is

      package Private_Iterable is

         --  Iterable aspect on full view of private type
         --    is disallowed in SPARK.

         type T is private;
      private
         type T is new Integer
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element);

         function First (X : T) return Integer is (0);
         function Next (X : T; Y : Integer) return Integer is (0);
         function Has_Element (X : T; Y : Integer) return Boolean is (False);
      end Private_Iterable;

      package Public_Iterable is

         --  Legal on public partial view.

         type T is private
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element);

         function First (X : T) return Integer is (0);
         function Next (X : T; Y : Integer) return Integer is (0);
         function Has_Element (X : T; Y : Integer) return Boolean is (False);
      private
         type T is new Integer;
      end Public_Iterable;

      package Fully_Private_Iterable is
      private

         -- Legal on private-only type.

         type T is new Integer
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element);

         function First (X : T) return Integer is (0);
         function Next (X : T; Y : Integer) return Integer is (0);
         function Has_Element (X : T; Y : Integer) return Boolean is (False);
      end Fully_Private_Iterable;
   end Iterable_And_Privacy;

   package Iterable_And_Dispatching is

      package Dispatching_Element is

         --  Iterable Primitive with controlling result (for Element)
         --  is forbidden.

         type T is (Holder)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         type Element_Type is tagged null record;
         function First (X : T) return Boolean is (True);
         function Next (X : T; Y : Boolean) return Boolean is (False);
         function Has_Element (X : T; Y : Boolean) return Boolean is (Y);
         function Element (X : T; Y : Boolean) return Element_Type
         is (null record);
      end Dispatching_Element;

      package Dispatching_Cursor is

         --  Iterable Primitive with controlling result (for cursor)
         --  is forbidden. That include case with cursor and elements
         --  coinciding.

         type T is (Holder)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Last        => First,
                             Previous    => Next,
                             Element     => Element);
         type Cursor_Type is tagged null record;
         function First (X : T) return Cursor_Type is (null record);
         function Next (X : T; Y : Cursor_Type) return Cursor_Type
         is (null record);
         function Has_Element (X : T; Y : Cursor_Type) return Boolean
         is (False);
         function Element (X : T; Y : Cursor_Type) return Cursor_Type is (Y);
      end Dispatching_Cursor;

      package Container_Dispatching is

         --  Dispatch on container is fine.
         --  Having tagged types for cursor/element is also fine
         --  (as long as non-dispatching)

         package Inner is
            type Cursor is tagged null record;
         end Inner;
         use Inner;
         type Container is tagged null record
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Last        => First,
                             Previous    => Next,
                             Element     => Element);
         function First (X : Container) return Cursor is (null record);
         function Next (X : Container; Y : Cursor) return Cursor is (Y);
         function Has_Element (X : Container; Y : Cursor) return Boolean
         is (False);
         function Element (X : Container; Y : Cursor) return Cursor is (Y);
      end Container_Dispatching;

   end Iterable_And_Dispatching;

   package Iterable_For_Proof_Contains_Reading_Global is
      type Singleton is (Uniq)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (C : Singleton) return Boolean is (True);
      function Next (C : Singleton; X : Boolean) return Boolean is (False);
      function Has_Element (C : Singleton; X : Boolean) return Boolean is (X);
      Flag : Boolean := True;
      function Hidden_Not (X : Boolean) return Boolean is (not X);
      function Contains (C : Singleton; X : Singleton) return Boolean is
        (Flag or Hidden_Not (Flag));
      function Element (C : Singleton; X : Boolean) return Singleton is (Uniq);
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
   end Iterable_For_Proof_Contains_Reading_Global;

   package Iterable_For_Proof_Model_Reading_Global is
      type Singleton is (Uniq)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      type Singleton_Model is (Version_1, Version_2)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (C : Singleton_Model) return Boolean is (True);
      function Next (C : Singleton_Model; X : Boolean) return Boolean
      is (False);
      function Has_Element (C : Singleton_Model; X : Boolean) return Boolean
      is (X);
      function Element (C : Singleton_Model; X : Boolean) return Boolean
      is (True);
      function First (C : Singleton) return Boolean is (True);
      function Next (C : Singleton; X : Boolean) return Boolean is (False);
      function Has_Element (C : Singleton; X : Boolean) return Boolean is (X);
      Flag : Boolean := True;
      function Model (C : Singleton) return Singleton_Model
      is (if Flag then Version_1 else Version_2);
      function Element (C : Singleton; X : Boolean) return Boolean is (True);
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Model);
   end Iterable_For_Proof_Model_Reading_Global;

begin
   null;
end Illegal;
