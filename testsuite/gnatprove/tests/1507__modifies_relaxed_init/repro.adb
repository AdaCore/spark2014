procedure Repro with SPARK_Mode is
   type Cell is record
      Value : Integer;
   end record
   with Relaxed_Initialization;

   type Elements_Array is array (Positive range <>) of Cell;
   type Links_Array is array (Positive range <>) of Natural;

   type List (Capacity : Positive) is record
      Links    : Links_Array (1 .. Capacity);
      Elements : Elements_Array (1 .. Capacity);
   end record;

   procedure Update (Container : in out List) is
      procedure Set_Link
      with Modifies => Container.Links;

      procedure Set_Link is
      begin
         Container.Links (1) := 0;
      end Set_Link;
   begin
      Set_Link;
   end Update;

   Container : List (1);
begin
   Container.Links := (others => 0);
   Update (Container);
end Repro;
