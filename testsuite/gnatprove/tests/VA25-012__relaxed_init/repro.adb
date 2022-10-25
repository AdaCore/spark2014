package body Repro
is
   procedure Update (Item : out Item_Type)
   is
      Data : Foo_Type with Relaxed_Initialization;
   begin
      Item := (A => True,
               B => Data,
               C => Data);
   end Update;
end Repro;
