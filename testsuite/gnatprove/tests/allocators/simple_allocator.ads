pragma Unevaluated_Use_Of_Old (Allow);
with Ada.Containers.Functional_Sets;

package Simple_Allocator with
  SPARK_Mode,
  Abstract_State    => State,
  Initializes       => State,
  Initial_Condition => All_Available
is
   Capacity : constant := 10_000;

   type Resource is new Integer range 0 .. Capacity;
   subtype Valid_Resource is Resource range 1 .. Capacity;

   No_Resource : constant Resource := 0;

   function Is_Available (Res : Resource) return Boolean;
   function Is_Allocated (Res : Resource) return Boolean;

   function All_Available return Boolean with Ghost;

   package M with Ghost is

      package S is new Ada.Containers.Functional_Sets (Element_Type => Resource);
      use S;

      type T is record
         Available : Set;
         Allocated : Set;
      end record;

      function "=" (X, Y : T) return Boolean is
        (X.Available = Y.Available
           and then
         X.Allocated = Y.Allocated);

      function Is_Valid (M : T) return Boolean;

      function Model return T with Post => Is_Valid (Model'Result);

   end M;

   use M; use M.S;

   procedure Alloc (Res : out Resource) with
     Contract_Cases =>

       --  When no resource is available, return the special value No_Resource
       --  with the allocator unmodified.

       (Is_Empty (Model.Available) =>
          Res = No_Resource
            and then
          Model = Model'Old,

        --  Otherwise, return an available resource which becomes allocated

        others =>
          Is_Add (Model.Available, Res, Result => Model.Available'Old)
            and then
          Is_Add (Model.Allocated'Old, Res, Result => Model.Allocated));

   procedure Free (Res : Resource) with
     Contract_Cases =>

       --  When the resource is allocated, make it available

       (Mem (Model.Allocated, Res) =>
          Is_Add (Model.Available'Old, Res, Result => Model.Available)
            and then
          Is_Add (Model.Allocated, Res, Result => Model.Allocated'Old),

        --  Otherwise, do nothing

        others =>
          Model = Model'Old);

end Simple_Allocator;
