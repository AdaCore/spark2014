procedure Main with SPARK_Mode is

   package Ptr_Accesses with
     Annotate => (GNATprove, Always_Return),
     Abstract_State => Allocated_Memory,
     Initializes => Allocated_Memory
   is
      type Ptr is private;

      function Create (V : Integer) return Ptr with
        Volatile_Function,
        Post => Get (Create'Result) = V;
      function Get (X : Ptr) return Integer with
        Global => Allocated_Memory;
      procedure Set (X : Ptr; V : Integer) with
        Global => (In_Out => Allocated_Memory),
        Post => Get (X) = V;
   private
      pragma SPARK_Mode (Off);
      type Ptr is access all Integer;
   end Ptr_Accesses;

   package body Ptr_Accesses
   with SPARK_Mode => Off
   is
      function Create (V : Integer) return Ptr is (new Integer'(V));
      function Get (X : Ptr) return Integer is (X.all);
      procedure Set (X : Ptr; V : Integer) is
      begin
         X.all := V;
      end Set;
   end Ptr_Accesses;

   procedure Ownership_Transfer with
     Global => (In_Out => Ptr_Accesses.Allocated_Memory)
   is
      X : Ptr_Accesses.Ptr := Ptr_Accesses.Create (1);
      Y : Ptr_Accesses.Ptr;
   begin
      pragma Assert (Ptr_Accesses.Get (X) = 1);
      Y := X;
      Ptr_Accesses.Set (Y, 2);
      pragma Assert (Ptr_Accesses.Get (X) = 2);
   end Ownership_Transfer;

   package Ptr_Accesses_2 with
     Annotate => (GNATprove, Always_Return)
   is
      type Ptr is limited private;
      function Create (V : Integer) return Ptr with
        Volatile_Function,
        Post => Get (Create'Result) = V;
      function Get (X : Ptr) return Integer with
        Global => null;
      procedure Set (X : in out Ptr; V : Integer) with
        Global => null,
        Post => Get (X) = V;
      procedure Swap (X, Y : in out Ptr) with
        Post => Get (X) = Get (Y)'Old and Get (Y) = Get (X)'Old;
   private
      pragma SPARK_Mode (Off);
      type Ptr is access all Integer;
   end Ptr_Accesses_2;

   package body Ptr_Accesses_2
   with SPARK_Mode => Off
   is
      function Create (V : Integer) return Ptr is (new Integer'(V));
      function Get (X : Ptr) return Integer is (X.all);
      procedure Set (X : in out Ptr; V : Integer) is
      begin
         X.all := V;
      end Set;
      procedure Swap (X, Y : in out Ptr) is
         Tmp : Ptr := X;
      begin
         X := Y;
         Y := Tmp;
      end Swap;
   end Ptr_Accesses_2;

   procedure Ownership_Transfer_2 with Global => null is
      X : Ptr_Accesses_2.Ptr := Ptr_Accesses_2.Create (1);
      Y : Ptr_Accesses_2.Ptr := Ptr_Accesses_2.Create (1);
   begin
      pragma Assert (Ptr_Accesses_2.Get (X) = 1);
      Ptr_Accesses_2.Swap (X, Y);
      Ptr_Accesses_2.Set (Y, 2);
      pragma Assert (Ptr_Accesses_2.Get (X) = 1);
   end Ownership_Transfer_2;

begin
   null;
end Main;
