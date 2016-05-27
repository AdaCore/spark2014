pragma Unevaluated_Use_Of_Old (Allow);
with Conts.Functional.Sequences;
pragma Elaborate_All (Conts.Functional.Sequences);
with Conts.Functional.Sets;
pragma Elaborate_All (Conts.Functional.Sets);
with Conts;
use type Conts.Count_Type;

package List_Allocator with
  SPARK_Mode,
  Abstract_State    => State,
  Initializes       => State,
  Initial_Condition => All_Available and Is_Valid
is
   pragma Elaborate_Body;

   Capacity : constant := 10_000;

   type Resource is new Integer range 0 .. Capacity;
   subtype Valid_Resource is Resource range 1 .. Capacity;

   No_Resource : constant Resource := 0;

   function Is_Available (Res : Resource) return Boolean;
   function Is_Allocated (Res : Resource) return Boolean;

   function All_Available return Boolean with Ghost;

   package M with Ghost,
     Initial_Condition =>
       (Is_Empty (Model.Allocated)
          and then
        Length (Model.Available) = Capacity
          and then
        Get (Model.Available, 1) = 1
          and then
        (for all RR in 1 .. Capacity => Get (Model.Available, RR) = Resource (RR))
          and then
        (for all RR in 1 .. Capacity => Mem (Model.Available, Resource (RR))))
   is
      package S1 is new Conts.Functional.Sequences (Index_Type => Positive,
                                                    Element_Type => Resource);
      use S1;

      package S2 is new Conts.Functional.Sets (Element_Type => Resource);
      use S2;

      type T is record
         Available : Sequence;
         Allocated : S2.Set;
      end record;

      function Mem (S : Sequence; E : Resource) return Boolean is
        (for some I in 1 .. Integer (Length (S)) => Get (S, I) = E);

      function "=" (X, Y : T) return Boolean is
        (X.Available = Y.Available
           and then
         X.Allocated = Y.Allocated);

      Model : T;

      function Is_Valid return Boolean;

   end M;

   use M; use M.S1; use M.S2;

   procedure Alloc (Res : out Resource) with
     Pre  => Is_Valid,
     Post => Is_Valid,
     Contract_Cases =>

       --  When no resource is available, return the special value No_Resource
       --  with the allocator unmodified.

       (Length (Model.Available) = 0 =>
          Res = No_Resource
            and then
          Model = Model'Old,

        --  Otherwise, return an available resource which becomes allocated

        others =>
          Is_Prepend (Model.Available, Res, Result => Model.Available'Old)
            and then
          Is_Add (Model.Allocated'Old, Res, Result => Model.Allocated));

   procedure Free (Res : Resource) with
     Pre  => Is_Valid,
     Post => Is_Valid,
     Contract_Cases =>

       --  When the resource is allocated, make it available

       (Mem (Model.Allocated, Res) =>
          Is_Prepend (Model.Available'Old, Res, Result => Model.Available)
            and then
          Is_Add (Model.Allocated, Res, Result => Model.Allocated'Old),

        --  Otherwise, do nothing

        others =>
          Model = Model'Old);

end List_Allocator;
