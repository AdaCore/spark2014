with System.Storage_Elements;
package body Volatile_Example_A
  with SPARK_Mode
is
   type Pair is record
      X, Y : Integer;
   end record;

   V : Integer
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#DEAD_BEEF#);

   W : Pair
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#00C0_FFEE#);

   procedure Do_Stuff
     with Global => (In_Out => (V, W));

   procedure Do_Stuff is
      Tmp : Pair;
   begin
      Tmp := W;  --  composite volatiles must be read and assigned whole
      if (Tmp.X > 0) then
         Tmp.X := V;
         Tmp.Y := V;
         pragma Assert (Tmp.X = Tmp.Y); -- not provable
      end if;
      W := Tmp;
   end Do_Stuff;
end Volatile_Example_A;
