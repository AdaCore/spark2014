with Interfaces;

procedure Overlay_Access with SPARK_Mode is
   type Ptr is access constant Integer;
   X : constant Ptr := null;
   Y : constant Interfaces.Unsigned_64
     with Import, Address => X'Address;
   type Holder is record
      Value : Ptr;
   end record;
   Bits : constant Interfaces.Unsigned_64 := 0;
   View : constant Holder with Import, Address => Bits'Address;
begin
   null;
end Overlay_Access;
