generic
   type Element_Type is private;

package Traces is
   pragma SPARK_Mode (On);

   type Cursor is private;

   type Trace is private
   with Iterable =>
     (First       => First,
      Next        => Next,
      Element     => Element,
      Has_Element => Has_Element);

   function Empty return Trace
     with Ghost, Import, Global => null;

   function Append (T : Trace; E : Element_Type) return Trace
     with Ghost, Import, Global => null;

   function First (T : Trace) return Cursor
     with Ghost, Import, Global => null;

   function Element (T : Trace; C : Cursor) return Element_Type
     with Ghost, Import, Global => null;

   function Has_Element (T : Trace; C : Cursor) return Boolean
     with Ghost, Import, Global => null;

   function Next (T : Trace; C : Cursor) return Cursor
     with Ghost, Import, Global => null;

   function Previous (T : Trace; C : Cursor) return Cursor
     with Ghost, Import, Global => null;

   function Is_First (T : Trace; C : Cursor) return Boolean
     with Ghost, Import, Global => null;

private
   pragma SPARK_Mode (Off);

   type Trace is new Integer;

   type Cursor is new Integer;

end Traces;
