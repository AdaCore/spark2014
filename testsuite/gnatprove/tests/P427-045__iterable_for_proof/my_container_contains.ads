package My_Container_Contains with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   Max : constant := 100;

   type Container is private with
     Iterable  => (First       => First,
                   Has_Element => Has_Element,
                   Next        => Next,
                   Element     => Element);

   type Cursor is private;

   function Mem (C : Container; E : Natural) return Boolean;

   function Valid (E : Natural) return Boolean;

   procedure Modify (C : in out Container) with
     Post => (for all E of C => Valid (E));

   function First (C : Container) return  Cursor;
   function Next (C : Container; P : Cursor) return Cursor with
     Pre => Has_Element (C, P);
   function Has_Element (C : Container; P : Cursor) return Boolean;
   function Element (C : Container; P : Cursor) return Natural with
     Pre  => Has_Element (C, P),
     Post => Mem (C, Element'Result);
   pragma Annotate
     (GNATprove, Iterable_For_Proof, "Contains", Entity => Mem);
private
   subtype My_Index is Natural range 1 .. Max;

   type Container is array (My_Index) of Natural;

       type Cursor is record
         Index : Natural;
      end record;
end My_Container_Contains;
