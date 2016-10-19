package Memregions
with
   SPARK_Mode,
   Abstract_State => State,
   Initializes    => State
is
   type Memory_Type is record
      Index : Natural := 0;
   end record;

   procedure Init;

   function Is_Valid return Boolean;

   function Get_Index (Idx : Positive) return Memory_Type
   with
      Global => (Input => State),
      Pre    => Is_Valid;

   generic
      with procedure Process (M : Memory_Type);
   procedure Memory_Has_Index (Idx : Natural)
   with
      Global => (Input => State),
      Pre    => Is_Valid;

   procedure Default_Process (M : Memory_Type);

end Memregions;
