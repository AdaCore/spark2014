pragma Unevaluated_Use_Of_Old (Allow);
with Functional_Sequences;
pragma Elaborate_All (Functional_Sequences);

package List_Allocator with
  SPARK_Mode,
  Abstract_State    => State,
  Initializes       => State,
  Initial_Condition => All_Available
is
   pragma Elaborate_Body;

   Capacity : constant := 3;

   type Resource is new Integer range 0 .. Capacity;
   subtype Valid_Resource is Resource range 1 .. Capacity;

   No_Resource : constant Resource := 0;

   function Is_Available (Res : Resource) return Boolean;
   function Is_Allocated (Res : Resource) return Boolean;

   function All_Available return Boolean with Ghost;

   package M is -- with Ghost is

      package S is new Functional_Sequences (Element_Type => Resource);
      use S;

      type T is record
         Available : Sequence;
         Allocated : Sequence;
      end record;

      function "=" (X, Y : T) return Boolean is
        (X.Available = Y.Available
           and then
         X.Allocated = Y.Allocated);

      Model : T;

      function Mem (S : Sequence; R : Resource) return Boolean is
        (for some J in 1 .. Length (S) => Get (S, J) = R);

      function Find (S : Sequence; R : Resource) return Natural with
        Contract_Cases =>
          (Mem (S, R) => Find'Result in 1 .. Length (S) and then Get (S, Find'Result) = R,
           others     => Find'Result = 0);

      function Is_Valid return Boolean;

   end M;

   use M; use M.S;

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
          Is_Prepend (Model.Allocated'Old, Res, Result => Model.Allocated));

   procedure Free (Res : Resource) with
     Pre  => Is_Valid,
     Post => Is_Valid,
     Contract_Cases =>

       --  When the resource is allocated, make it available

       (Mem (Model.Allocated, Res) =>
          Is_Prepend (Model.Available'Old, Res, Result => Model.Available)
            and then
          Length (Model.Allocated) = Length (Model.Allocated)'Old - 1
            and then
          (for all J in 1 .. Length (Model.Allocated)'Old =>
             (if Get (Model.Allocated'Old, J) /= Res then
                Mem (Model.Allocated, Get (Model.Allocated'Old, J)))),

        --  Otherwise, do nothing

        others =>
          Model = Model'Old);

end List_Allocator;
