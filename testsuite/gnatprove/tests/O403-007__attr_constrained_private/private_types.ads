package Private_Types with SPARK_Mode is

   type Simple (D : Natural := 0) is private;
   subtype S_Simple is Simple (D => 0);

   procedure Private_ReInit (S : in out Simple) with
     Pre  => S.D = 0 or else not S'Constrained,
     Post => S.D = 0;

private
   pragma SPARK_Mode (Off);

   type Nat_Access is access Natural;

   type Simple (D : Natural := 0) is record
      F1 : Nat_Access;
   end record;
end Private_Types;
