package body Bounded_Queue_V2 is

   function Full (Queue : in Queue_Type) return Boolean is
   begin
      return Queue.Count = Queue.Max_Size;
   end Full;

   function Empty (Queue : in Queue_Type) return Boolean is
   begin
      return Queue.Count = 0;
   end Empty;

   function Size (Queue : in Queue_Type) return Natural is
   begin
      return Queue.Count;
   end Size;

   function First_Element (Queue : in Queue_Type) return Element_Type is
   begin
      return Queue.Items (Queue.Front);
   end First_Element;

   function Last_Element (Queue : in Queue_Type) return Element_Type is
   begin
      return Queue.Items (Queue.Rear);
   end Last_Element;

   procedure Clear (Queue : in out Queue_Type) is
   begin
      Queue.Count := 0;
      Queue.Front := 1;
      Queue.Rear  := Queue.Max_Size;
   end Clear;

   procedure Enqueue (Queue : in out Queue_Type;
                      Item  : in     Element_Type) is
   begin
      Queue.Rear := Queue.Rear rem Queue.Max_Size + 1;
      Queue.Items (Queue.Rear) := Item;
      Queue.Count := Queue.Count + 1;
   end Enqueue;

   procedure Dequeue (Queue : in out Queue_Type;
                      Item  :    out Element_Type) is
   begin

      Item := Queue.Items (Queue.Front);
      Queue.Front := Queue.Front rem Queue.Max_Size + 1;
      Queue.Count := Queue.Count - 1;
   end Dequeue;

end Bounded_Queue_V2;

