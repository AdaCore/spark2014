package body Generic_Queue_Pack is

   procedure Enqueue
     (Queue : in out T_Queue;
      Item  : T_Element) is
   begin
      if Queue.Count = Queue.Container'Length then
         return;
      end if;

      Queue.Container (Queue.Rear) := Item;
      Queue.Rear := (if Queue.Rear = Queue.Container'Length then
                        1
                     else
                        Queue.Rear + 1);

      Queue.Count := Queue.Count + 1;
   end Enqueue;

   procedure Dequeue
     (Queue : in out T_Queue;
      Item  : out T_Element) is
   begin
      if Queue.Count = 0 then
         return;
      end if;

      Item := Queue.Container (Queue.Front);
      Queue.Front := (if Queue.Front = Queue.Container'Length then
                         1
                      else
                         Queue.Front + 1);
      Queue.Count := Queue.Count - 1;
   end Dequeue;

   procedure Reset (Queue : in out T_Queue) is
   begin
      Queue.Count := 0;
   end Reset;

   function Is_Empty (Queue : T_Queue) return Boolean is
   begin
      return Queue.Count = 0;
   end Is_Empty;

   function Is_Full (Queue : T_Queue) return Boolean is
   begin
      return Queue.Count = Queue.Container'Length;
   end Is_Full;

   protected body Protected_Queue is

      procedure Enqueue_Item
        (Item         : T_Element;
         Has_Succeed  : out Boolean) is
      begin
         if not Is_Full (Queue) then
            Has_Succeed := True;
            Enqueue (Queue, Item);
            Data_Available := True;
         else
            Has_Succeed := False;
         end if;

      end Enqueue_Item;

      procedure Dequeue_Item
        (Item        : out T_Element;
         Has_Succeed : out Boolean) is
      begin
         if not Is_Empty (Queue) then
            Has_Succeed := True;
            Dequeue (Queue, Item);
            Data_Available := not Is_Empty (Queue);
         else
            Has_Succeed := False;
         end if;
      end Dequeue_Item;

      procedure Reset_Queue is
      begin
         Reset (Queue);
      end Reset_Queue;

      entry Await_Item_To_Dequeue
        (Item : out T_Element) when Data_Available is
      begin
         Dequeue (Queue, Item);
         Data_Available := not Is_Empty (Queue);
      end Await_Item_To_Dequeue;

   end Protected_Queue;

end Generic_Queue_Pack;
