--  Introduce a non executable type for maps with size 0. It can be used to
--  model a ghost subprogram parameter or a ghost component.

generic
   type Key_Type is private;
   No_Key : Key_Type;
   type Object_Type (<>) is private;

package Abstract_Maps with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   type Map is private with
     Iterable => (First       => Iter_First,
                  Next        => Iter_Next,
                  Has_Element => Has_Key);

   function Empty_Map return Map with
     Global => null,
     Post => (for all K in Empty_Map'Result => False);

   function Has_Key (M : Map; K : Key_Type) return Boolean with
     Import,
     Global => null,
     Post => (if Has_Key'Result then K /= No_Key);

   function Get (M : Map; K : Key_Type) return Object_Type with
     Import,
     Global => null,
     Pre => Has_Key (M, K);

   --  For quantification only. Do not use to iterate through the map.
   function Iter_First (M : Map) return Key_Type with
     Global => null,
     Import;
   function Iter_Next (M : Map; K : Key_Type) return Key_Type with
     Global => null,
     Import;

   type Ownership_Map is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function "+" (M : Ownership_Map) return Map with
     Global => null;

   function Is_Empty (M : Ownership_Map) return Boolean is
     (for all K in +M => False)
   with Global => null,
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   function Empty_Map return Ownership_Map with
     Global => null,
     Post => Is_Empty (Empty_Map'Result);

private
   pragma SPARK_Mode (Off);

   type Map is null record;

   function Empty_Map return Map is ((others => <>));

   type Ownership_Map is new Map;

   function "+" (M : Ownership_Map) return Map is
     (Map (M));

   function Empty_Map return Ownership_Map is ((others => <>));
end Abstract_Maps;
